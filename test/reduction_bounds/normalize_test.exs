defmodule ReductionBounds.NormalizeTest do
  use ExUnit.Case, async: true
  @moduletag timeout: 300_000

  alias ReductionBounds.{CoreFragment, CoreSource, Normalize, ProofInput, SearchBound}
  alias ReductionBounds.TestFixtures

  setup_all do
    {module, beam} = TestFixtures.bounded_counter()
    %{fixture: module, beam: beam}
  end

  test "uses the fixture map match and alias binding to justify a read", %{
    fixture: module,
    beam: beam
  } do
    program = fixture_program(module, :read_checked, beam)
    result = Normalize.normalize(program)

    assert %{
             program: %{
               expression:
                 {:case_map, {:var, input}, %{fields: [{"balance", _}]},
                  {:let_in, alias_name, {:var, input}, {:field, {:var, alias_name}, "balance"}},
                  outer_fallback},
               opaque: opaque
             },
             certificates: [
               %{
                 path: [:matched, :body],
                 facts: facts,
                 original:
                   {:case_map, {:var, alias_name}, %{tag: nil, fields: [{"balance", binder}]},
                    {:var, binder}, {:opaque, id} = fallback},
                 normalized: {:field, {:var, alias_name}, "balance"},
                 rewrite: {:read_field, alias_name, "balance", binder, fallback}
               }
             ]
           } = result

    assert {alias_name, "balance"} in facts
    assert Map.has_key?(opaque, id)
    assert opaque == program.opaque
    assert elem(program.expression, 4) == outer_fallback
  end

  test "retains the unchecked read and its fallback", %{fixture: module, beam: beam} do
    program = fixture_program(module, :read_unchecked, beam)
    assert %{program: ^program, certificates: []} = Normalize.normalize(program)
  end

  test "applies a supplied field assumption only to its subject and key" do
    original = field_case("state", "balance")
    program = program(original)
    matching = [{"state", "balance"}]

    assert %{
             program: %{expression: {:field, {:var, "state"}, "balance"}},
             certificates: [%{path: [], facts: ^matching, original: ^original}]
           } = Normalize.normalize(program, matching)

    for wrong <- [[{"other", "balance"}], [{"state", "limit"}]] do
      assert %{program: ^program, certificates: []} = Normalize.normalize(program, wrong)
    end
  end

  test "does not remove a match that returns a different value" do
    original = put_elem(field_case("state", "balance"), 3, {:int, 0})
    program = program(original)

    assert %{program: ^program, certificates: []} =
             Normalize.normalize(program, [{"state", "balance"}])
  end

  test "does not carry successful match facts into the fallback" do
    pattern = %{tag: nil, fields: [{"balance", "value"}]}
    read = field_case("state", "balance")
    program = program({:case_map, {:var, "state"}, pattern, read, read})

    assert %{
             program: %{
               expression:
                 {:case_map, {:var, "state"}, ^pattern, {:field, {:var, "state"}, "balance"},
                  ^read}
             },
             certificates: [%{path: [:matched]}]
           } = Normalize.normalize(program)
  end

  test "does not carry a guarded clause's bindings into its fallback" do
    pattern = %{tag: nil, fields: [{"balance", "value"}]}
    read = field_case("state", "balance")
    original = {:case_map_guarded, {:var, "state"}, pattern, read, read, read}

    assert %{
             program: %{
               expression:
                 {:case_map_guarded, _, ^pattern, {:field, _, "balance"}, {:field, _, "balance"},
                  ^read}
             },
             certificates: [%{path: [:condition]}, %{path: [:matched]}]
           } = Normalize.normalize(program(original))
  end

  test "Lean rejects a certificate missing the required fact", %{fixture: module, beam: beam} do
    assert %{certificates: [certificate]} =
             Normalize.normalize(fixture_program(module, :read_checked, beam))

    assert %{status: :error, diagnostics: [_ | _]} =
             verify(ProofInput.certificate_source([%{certificate | facts: []}]))
  end

  test "Lean rejects a fabricated field fact at an unchecked read", %{fixture: module, beam: beam} do
    {source, %{parameters: [input]} = program} = fixture_source(module, :read_unchecked, beam)
    %{program: normalized, certificates: [_]} = Normalize.normalize(program, [{input, "balance"}])

    assert %{status: :error, diagnostics: diagnostics} =
             verify(
               ProofInput.normalization_source(source, program.expression, normalized.expression)
             )

    assert Enum.any?(diagnostics, &(&1.severity == :error and &1.message =~ ~s(key := "balance")))
  end

  test "Lean rejects a decoded expression that differs from the extracted Core", %{
    fixture: module,
    beam: beam
  } do
    {source, program} = fixture_source(module, :read_checked, beam)
    changed = {:atom, "changed"}

    assert program.expression != changed

    assert %{status: :error, diagnostics: diagnostics} =
             verify(ProofInput.normalization_source(source, changed, changed))

    assert Enum.any?(
             diagnostics,
             &(&1.severity == :error and &1.message =~ "extractedCore.lower")
           )
  end

  test "discards facts when a binding shadows the subject" do
    read = field_case("state", "balance")

    for expression <- [
          {:let_in, "state", {:int, 0}, read},
          {:case_map, {:var, "state"}, %{tag: nil, fields: [{"balance", "state"}]}, read,
           {:opaque, "fallback"}}
        ] do
      program = program(expression)

      assert %{program: ^program, certificates: []} =
               Normalize.normalize(program, [{"state", "balance"}])
    end
  end

  defp fixture_program(module, name, beam) do
    {:ok, core} = SearchBound.core_function({module, name, 1}, [beam])
    {:ok, program} = CoreFragment.decode(core)
    program
  end

  defp fixture_source(module, name, beam) do
    {:ok, core} = SearchBound.core_function({module, name, 1}, [beam])
    {:ok, program} = CoreFragment.decode(core)
    {:ok, source} = CoreSource.serialize(core, program.opaque)
    {source, program}
  end

  defp verify(source) do
    proof = %Lynx.Lean{
      file: "normalization_test.lean",
      span: {1, 1},
      indentation: 0,
      source: source
    }

    assert {:ok, postludes} = ProofInput.postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    reports =
      ReductionBounds.Verification.verify!(translation,
        postlude_imports: ["Erlang.erlang", "Erlang.maps"]
      )

    assert Enum.all?(Enum.drop(reports, -1), &(&1.status == :ok))
    assert %{module: "Erlang.postlude"} = report = List.last(reports)
    report
  end

  defp field_case(subject, key) do
    {:case_map, {:var, subject}, %{tag: nil, fields: [{key, "result"}]}, {:var, "result"},
     {:opaque, "fallback"}}
  end

  defp program(expression), do: %{parameters: ["state"], expression: expression, opaque: %{}}
end

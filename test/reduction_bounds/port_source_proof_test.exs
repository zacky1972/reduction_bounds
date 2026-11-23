defmodule ReductionBounds.PortSourceProofTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{PortProtocol, PortSourceProof, ProofInput, ProtocolCost, ProtocolSize}
  alias ReductionBounds.Fixtures.{PortClient, PortHelpers}

  @moduletag :port_source

  for function <- [:request, :reordered] do
    @function function
    test "public API checks #{@function} from compiled Core through the caller budget" do
      assert {:ok, bound} =
               ReductionBounds.infer_port_bound({PortClient, @function, 2}, profile(), options())

      assert bound.source_correspondence == :checked
      assert bound.lean_status == :checked
      assert bound.verification_scope.kind == :core_connected_port_client
      assert bound.execution_domain == :finite_normal_executions_under_call_contracts
      assert Enum.all?(bound.reports, &(&1.status == :ok))
      assert :exceptions in bound.unverified
      assert :termination in bound.unverified
    end
  end

  for {label, from, to} <- [
        {:helper_identity, ~S|"Elixir.ReductionBounds.Fixtures.PortHelpers", "decode"|,
         ~S|"Elixir.ReductionBounds.Fixtures.PortHelpers", "prepare"|},
        {:submission_options, ~S|(.literal (.cons (.atom "nosuspend") .nil))|,
         ~S|(.literal .nil)|},
        {:branch_orientation, "true (.replyCase", "false (.replyCase"},
        {:primitive_identity, ~S|(.boolCase ⟨"erlang", "port_command"|,
         ~S|(.boolCase ⟨"erlang", "wrong_command"|},
        {:local_budget, "suppliedCore.budget = 25", "suppliedCore.budget = 0"},
        {:returned_formula, "def suppliedSourceFormula : ReductionBounds.ProtocolCost.Expr :=",
         "def suppliedSourceFormula : ReductionBounds.ProtocolCost.Expr := .add (.constant 1)"}
      ] do
    @from from
    @to to
    test "Lean rejects altered #{label} evidence" do
      {:ok, _, proof} = PortSourceProof.build({PortClient, :request, 2}, profile(), options())
      changed = String.replace(proof.source, @from, @to, global: false)
      refute changed == proof.source, @from
      assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
    end
  end

  test "Lean rejects an unfinished connection certificate" do
    {:ok, _, proof} = PortSourceProof.build({PortClient, :request, 2}, profile(), options())

    changed =
      Regex.replace(
        ~r/(theorem suppliedConnection[^\n]+:=)\n[^\n]+/,
        proof.source,
        "\\1 by sorry"
      )

    refute changed == proof.source
    assert Enum.any?(reports(%{proof | source: changed}), &(&1.status == :error))
  end

  defp options,
    do: [
      beam_binaries: ReductionBounds.TestFixtures.port_client_beams(),
      calls: %{
        prepare: {PortHelpers, :prepare, 1},
        reply: {PortHelpers, :await_reply, 1},
        decode: {PortHelpers, :decode, 1}
      }
    ]

  defp profile do
    {:ok, conditions} =
      PortProtocol.conditions(
        data_bounds:
          Map.new([:request, :response, :message], &{&1, %ProtocolSize{bytes: 8, structure: 16}}),
        count_bounds: %{
          total_events: 30,
          submission_attempts: 4,
          submission_events: 8,
          resumptions: 3,
          retries: 3,
          receive_inspections: 8
        }
      )

    rules =
      for {{_, event} = context, _} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{},
          do: {context, %{counter: :total_events, cost: {:charge, :local}}}

    {:ok, profile} = ProtocolCost.new(conditions, rules)
    profile
  end

  defp reports(proof) do
    {:ok, postludes} = ProofInput.port_source_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    Lynx.Commands.verify!(project, ProofInput.assemble(translation))
  end
end

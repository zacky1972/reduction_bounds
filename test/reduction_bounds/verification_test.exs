defmodule ReductionBounds.VerificationTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.Verification

  setup do
    previous = System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS")
    System.delete_env("REDUCTION_BOUNDS_BENCH_EVENTS")

    on_exit(fn ->
      if previous,
        do: System.put_env("REDUCTION_BOUNDS_BENCH_EVENTS", previous),
        else: System.delete_env("REDUCTION_BOUNDS_BENCH_EVENTS")
    end)
  end

  test "finalizes explicit imports without enabling verification caches" do
    [file] =
      Verification.assemble(translation("theorem sample : True := by trivial"),
        postlude_imports: ["Erlang.maps", "Erlang.maps", "Erlang.erlang"]
      )

    assert file["module"] == "Erlang.postlude"
    assert Enum.take(file["imports"], 2) == ["Erlang.maps", "Erlang.erlang"]
    refute Map.has_key?(file, "cache_key")
  end

  @tag :tmp_dir
  test "measures successful verification without changing its reports", %{tmp_dir: dir} do
    source = translation("theorem sample : True := by trivial")
    original = Verification.verify!(source)
    assert [%{status: :ok, module: "Erlang.postlude"}] = original
    path = Path.join(dir, "events.jsonl")
    System.put_env("REDUCTION_BOUNDS_BENCH_EVENTS", path)
    reports = Verification.verify!(source)

    assert Enum.map(reports, &Map.drop(&1, [:time_ms])) ==
             Enum.map(original, &Map.drop(&1, [:time_ms]))

    [started, completed] = events(path)
    assert started["event"] == "started"
    assert completed["event"] == "completed"
    assert completed["id"] == started["id"]
    assert completed["runner_wall_ms"] >= completed["module_wall_ms"]
    assert completed["reports"] |> hd() |> Map.fetch!("cached") == false
    assert completed["reports"] |> hd() |> Map.fetch!("theorems") == []
  end

  @tag :tmp_dir
  test "retains verification errors and ignores an unusable measurement destination", %{
    tmp_dir: dir
  } do
    System.put_env("REDUCTION_BOUNDS_BENCH_EVENTS", dir)
    reports = Verification.verify!(translation("theorem invalid : False := by trivial"))
    assert Enum.any?(reports, &(&1.status == :error))

    assert Enum.any?(
             reports,
             &Enum.any?(&1.diagnostics, fn diagnostic -> diagnostic.severity == :error end)
           )
  end

  @tag :tmp_dir
  test "records and reraises assembly exceptions", %{tmp_dir: dir} do
    path = Path.join(dir, "events.jsonl")
    System.put_env("REDUCTION_BOUNDS_BENCH_EVENTS", path)

    assert_raise KeyError, fn ->
      Verification.verify!(translation(""), definition: :translated)
    end

    [_, failed] = events(path)
    assert failed["event"] == "failed"
    assert failed["kind"] == "error"
  end

  defp translation(source) do
    proof = %Lynx.Lean{source: source, file: "boundary_test.lean", span: {1, 1}, indentation: 0}
    Lynx.Translation.new(postludes: [proof])
  end

  defp events(path),
    do: path |> File.read!() |> String.split("\n", trim: true) |> Enum.map(&JSON.decode!/1)
end

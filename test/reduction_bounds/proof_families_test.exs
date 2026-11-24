defmodule ReductionBounds.ProofFamilySupport do
  alias ReductionBounds.ProofModules

  def scenarios do
    [
      core: [:normalize, :execution],
      integer: [:integer_cost_source, :bound_transfer],
      protocol: [:protocol_cost, :port_completion, :port_source],
      lists: [:search, :list_primitives],
      buffer: [:circular_buffer_sequence]
    ]
  end

  def input(roots) do
    proof = %Lynx.Lean{
      source: "theorem familySmoke : True := by trivial",
      file: "family_smoke.lean",
      span: {1, 1},
      indentation: 0
    }

    Lynx.Translation.new(postludes: ProofModules.load(roots) ++ [proof])
  end
end

defmodule ReductionBounds.ProofFamiliesTest do
  use ExUnit.Case,
    async: true,
    parameterize:
      for(
        {scenario, _roots} <- ReductionBounds.ProofFamilySupport.scenarios(),
        do: %{scenario: scenario}
      )

  alias ReductionBounds.{ProofFamilySupport, Verification}
  @moduletag timeout: 300_000

  setup context do
    ReductionBounds.TestFixtures.label_scenario(context)
  end

  test "theories verify through named, reused, bypassed, and embedded paths", %{scenario: family} do
    input = ProofFamilySupport.input(Keyword.fetch!(ProofFamilySupport.scenarios(), family))

    for options <- [
          [cache: true, shared_modules: true],
          [cache: true, shared_modules: true],
          [cache: false, shared_modules: true],
          [cache: false, shared_modules: false]
        ] do
      reports = Verification.verify!(input, options)
      assert reports != []
      assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
      assert List.last(reports).module == "Erlang.postlude"
      if options[:cache] == false, do: refute(Enum.any?(reports, & &1.cached))
    end
  end
end

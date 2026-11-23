defmodule ReductionBounds.Benchmark.Workloads do
  @moduledoc false

  alias ReductionBounds.{
    CostContract,
    IntegerSize,
    PortProtocol,
    ProtocolConditions,
    ProtocolCost,
    ProtocolSize
  }

  @spec names() :: [String.t()]
  def names(),
    do: ~w(integer_cost bound_transfer list circular_buffer port runner_empty runner_runtime)

  @spec run(String.t()) :: :ok
  def run("runner_empty") do
    [] = ReductionBounds.Verification.verify!([])
    :ok
  end

  def run("runner_runtime") do
    proof = %Lynx.Lean{
      file: "benchmark_probe.lean",
      span: {1, 1},
      indentation: 0,
      source: "theorem benchmarkProbe : True := by trivial"
    }

    reports = ReductionBounds.Verification.verify!(Lynx.Translation.new(postludes: [proof]))
    true = reports != [] and Enum.all?(reports, &(&1.status == :ok))
    :ok
  end

  def run("list") do
    {:ok, _result} = ReductionBounds.infer_list_bound({:lists, :member, 2})
    :ok
  end

  def run("circular_buffer") do
    {:ok, _result} = ReductionBounds.infer_circular_buffer_bound()
    :ok
  end

  def run(name) when name in ["integer_cost", "bound_transfer"] do
    beam = compile_program()
    functions = Map.new(CostContract.operations(), &{&1, {:add, 2, {:max, :left, :right}}})
    {:ok, source} = CostContract.new(id: :benchmark_source, functions: functions)

    {:ok, bound} =
      ReductionBounds.infer_integer_cost_bound({__MODULE__.Program, :product, 1},
        beam_binaries: [beam],
        input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}],
        cost_contract: source
      )

    if name == "bound_transfer" do
      functions = Map.new(CostContract.operations(), &{&1, {:add, 1, {:max, :left, :right}}})
      {:ok, destination} = CostContract.new(id: :benchmark_destination, functions: functions)

      {:ok, _result} =
        ReductionBounds.transfer_integer_bound(bound, destination, beam_binaries: [beam])
    end

    :ok
  end

  def run("port") do
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
      for {{_, event} = context, rule} <- conditions.rules,
          elem(conditions.contract.events[event], 0) != nil,
          into: %{},
          do:
            {context,
             %{counter: List.first(rule.counts) || :total_events, cost: {:charge, :event_work}}}

    {:ok, profile} = ProtocolCost.new(conditions, rules)
    {:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})

    {:ok, _result} =
      ReductionBounds.verify_port_model(profile, [:prepare, :submit_accepted],
        observations: %{0 => observation, 1 => observation}
      )

    :ok
  end

  defp compile_program() do
    [{_module, beam}] =
      Code.compile_string("""
      defmodule #{__MODULE__}.Program do
        @compile :debug_info
        def product(x), do: x * x + 1
      end
      """)

    beam
  end
end

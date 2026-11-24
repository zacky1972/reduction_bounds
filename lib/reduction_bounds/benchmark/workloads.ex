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
    do:
      ~w(integer_analysis integer_cost bound_transfer contract_comparison search list composed circular_buffer circular_buffer_sequence struct execution periodic port port_source runner_empty runner_runtime)

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

  def run("circular_buffer_sequence") do
    {:ok, _result} = ReductionBounds.infer_circular_buffer_sequence_bound()
    :ok
  end

  def run("contract_comparison") do
    {:ok, smaller} =
      CostContract.new(
        id: :benchmark_smaller,
        functions: Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
      )

    {:ok, larger} =
      CostContract.new(
        id: :benchmark_larger,
        functions: Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
      )

    {:ok, _result} = ReductionBounds.compare_cost_contracts(smaller, larger)
    :ok
  end

  def run(name) when name in ["search", "composed", "struct", "execution", "periodic"] do
    beam = compile_program()
    {:ok, _result} = program_workload(name, beam)
    :ok
  end

  def run("integer_analysis") do
    beam = compile_program()

    {:ok, _result} =
      ReductionBounds.infer_integer_sizes({__MODULE__.Program, :product, 1},
        beam_binaries: [beam],
        input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}]
      )

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
    profile = port_profile()
    {:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})

    {:ok, _result} =
      ReductionBounds.verify_port_model(profile, [:prepare, :submit_accepted],
        observations: %{0 => observation, 1 => observation}
      )

    :ok
  end

  def run("port_source") do
    beam = compile_program()

    {:ok, _result} =
      ReductionBounds.infer_port_bound({__MODULE__.Program, :request, 2}, port_profile(),
        beam_binaries: [beam],
        calls: %{
          prepare: {__MODULE__.Helpers, :prepare, 1},
          reply: {__MODULE__.Helpers, :await_reply, 1},
          decode: {__MODULE__.Helpers, :decode, 1}
        }
      )

    :ok
  end

  defp port_profile() do
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
    profile
  end

  defp program_workload("search", beam),
    do:
      ReductionBounds.infer_search_bound({__MODULE__.Program, :contains, 2},
        beam_binaries: [beam]
      )

  defp program_workload("composed", beam),
    do:
      ReductionBounds.infer_list_bound({__MODULE__.Program, :reverse_twice, 1},
        beam_binaries: [beam]
      )

  defp program_workload("struct", beam),
    do:
      ReductionBounds.infer_struct_bound({__MODULE__.Program, :read_checked, 1},
        beam_binaries: [beam]
      )

  defp program_workload("execution", beam),
    do:
      ReductionBounds.infer_verified_bound({__MODULE__.Program, :run, 1},
        beam_binaries: [beam],
        call_contracts: %{{__MODULE__.Helpers, :step, 1} => 5}
      )

  defp program_workload("periodic", beam),
    do:
      ReductionBounds.infer_periodic_bound({__MODULE__.Program, :enqueue_pair, 2},
        beam_binaries: [beam]
      )

  defp compile_program() do
    modules =
      Code.compile_string("""
      defmodule #{__MODULE__}.Helpers do
        def step(n), do: n + 1
        def prepare(input), do: input
        def await_reply(port) do
          receive do
            {^port, {:data, input}} -> {:data, input}
            {^port, :closed} -> :closed
          after
            0 -> :timeout
          end
        end
        def decode(input), do: input
      end
      defmodule #{__MODULE__}.Program do
        @compile :debug_info
        defstruct balance: 0
        alias #{__MODULE__}.Helpers
        def product(x), do: x * x + 1
        def contains(_key, []), do: false
        def contains(key, [head | _]) when head === key, do: true
        def contains(key, [_ | tail]), do: contains(key, tail)
        def read_checked(%__MODULE__{balance: _} = counter), do: counter.balance
        def run(0), do: 0
        def run(n) do
          x = Helpers.step(n)
          x + run(n - 1)
        end
        def reverse_twice(xs) do
          reversed = :lists.reverse(xs, [0])
          :lists.reverse(reversed, [])
        end
        def enqueue_pair(state, period) do
          advanced = state + 2
          if advanced >= period, do: {advanced - period, true}, else: {advanced, false}
        end
        def request(port, input) do
          prepared = Helpers.prepare(input)
          case :erlang.port_command(port, prepared, [:nosuspend]) do
            true ->
              case Helpers.await_reply(port) do
                {:data, data} -> Helpers.decode(data)
                :closed -> :closed
                :timeout -> :timeout
              end
            false -> :rejected
          end
        end
      end
      """)

    {_module, beam} = List.keyfind(modules, __MODULE__.Program, 0)
    beam
  end
end

defmodule ReductionBounds.PortSource do
  @moduledoc """
  Reifies a finite, contracted Port-client fragment from BEAM debug information.

  The target has two arguments: the Port and the preparation input. Supported
  blocks are a static preparation binding, a Boolean case on
  `:erlang.port_command(port, request, [:nosuspend])`, a static response-helper
  case with `{:data, payload}`, `:closed`, and `:timeout` patterns, and a static
  decoding call. Boolean and reply clauses may be reordered. All guards must
  be literal true; the compiler-generated case failure is retained as an
  excluded outcome under the declared call-result contracts.

  Helper contracts are explicit assumptions, not inferred properties of their
  implementations. Native receive, recursion, dynamic calls, blocking command
  submission, exceptions and other unsupported syntax report the target and
  source path. Proof generation and checking are provided by the source proof
  builder. Source extraction and reification remain trusted boundaries.
  """

  alias ReductionBounds.{PortProtocol, ProtocolCost, SearchBound}

  @roles [:prepare, :reply, :decode]

  @spec infer(ReductionBounds.target(), ProtocolCost.t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def infer(target, profile, options \\ [])

  def infer({module, function, arity} = target, profile, options)
      when is_atom(module) and is_atom(function) and is_integer(arity) and arity >= 0 do
    with {:ok, settings} <- settings(options),
         {:ok, checked} <- ProtocolCost.check_trace(profile, []),
         {:ok, contract} <- PortProtocol.new(),
         true <- profile.conditions.contract == contract,
         {:ok, core} <- SearchBound.core_function(target, settings.beam_binaries) do
      {:ok, candidate(core, target, checked, settings.calls)}
    else
      false -> {:error, :unsupported_port_contract}
      {:error, reason} -> {:error, {:port_source, target, reason}}
    end
  catch
    {:port_source, reason} -> {:error, {:port_source, target, reason}}
  end

  def infer(target, _profile, _options), do: {:error, {:port_source, target, :invalid_target}}

  defp settings(options) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, beam_binaries: [], calls: %{}),
         true <- valid_beams?(options[:beam_binaries]),
         :ok <- validate_calls(options[:calls]) do
      {:ok, Map.new(options)}
    else
      false -> {:error, :invalid_port_source_options}
      error -> error
    end
  end

  defp valid_beams?([]), do: true
  defp valid_beams?([beam | rest]), do: is_binary(beam) and valid_beams?(rest)
  defp valid_beams?(_beams), do: false

  defp validate_calls(calls) when is_map(calls) and not is_struct(calls) do
    missing = @roles -- Map.keys(calls)

    cond do
      missing != [] ->
        {:error, {:missing_port_call_contracts, missing}}

      Enum.sort(Map.keys(calls)) != Enum.sort(@roles) ->
        {:error, :unknown_port_call_contract}

      not Enum.all?(calls, fn {_role, mfa} -> valid_helper?(mfa) end) ->
        {:error, :invalid_port_call_contract}

      length(Enum.uniq(Map.values(calls))) != 3 ->
        {:error, :ambiguous_port_call_contracts}

      true ->
        :ok
    end
  end

  defp validate_calls(_calls), do: {:error, :invalid_port_call_contracts}

  defp valid_helper?({module, name, 1}),
    do: is_atom(module) and is_atom(name) and module != :erlang

  defp valid_helper?(_mfa), do: false

  defp candidate({:c_fun, _, [{:c_var, _, port}, {:c_var, _, _}], body}, target, checked, calls) do
    source = lower(body, [])
    context = %{state: :idle, port: variable(port), request: "", data: ""}
    {model, certificate} = connect(source, context, calls, [])
    budget = budget(source)
    caller = checked.upper_bounds.caller

    bounds =
      Map.put(checked.upper_bounds, :caller, %{
        caller
        | formula: {:add, {:mul, budget, {:charge, :source_node}}, caller.formula}
      })

    Map.merge(checked, %{
      source: :port_source,
      target: target,
      core_source: source,
      model: model,
      connection: certificate,
      source_node_bound: budget,
      upper_bounds: bounds,
      context: context,
      calls: calls,
      source_correspondence: :certificate_pending,
      verification_scope: :finite_normal_executions_under_call_contracts,
      call_contracts:
        Map.new(calls, fn {role, mfa} ->
          {role,
           %{
             target: mfa,
             status: :assumed,
             work_coverage: :protocol_event_charges,
             result_contract: role,
             totality: :not_established
           }}
        end),
      primitive_contracts: [
        %{target: {:erlang, :port_command, 3}, options: [:nosuspend], status: :assumed}
      ],
      trusted: [:beam_debug_extraction, :core_reification, :serialization],
      unverified: [
        :helper_implementations,
        :input_contracts,
        :framing_and_matching,
        :exceptions,
        :source_prefixes,
        :termination,
        :runtime_correspondence,
        :wall_clock_time
      ]
    })
  end

  defp candidate(_core, _target, _checked, _calls), do: fail({:unsupported_function_arity, [], 2})

  defp lower({:c_let, _, [{:c_var, _, binder}], rhs, body}, path),
    do: {:let_call, variable(binder), call(rhs, path ++ [:binding]), lower(body, path ++ [:body])}

  defp lower({:c_case, _, subject, clauses}, path) do
    source_call = call(subject, path ++ [:subject])
    {branches, [fallback]} = Enum.split(clauses, -1)
    if not fallback?(fallback), do: fail({:unsupported_case_fallback, path})
    lower_case(source_call, branches, path)
  end

  defp lower({:c_call, _, _, _, _} = core, path), do: {:tail_call, call(core, path)}
  defp lower({:c_var, _, _} = core, path), do: {:ret, arg(core, path)}
  defp lower({:c_literal, _, _} = core, path), do: {:ret, arg(core, path)}
  defp lower(core, path), do: fail({:unsupported_expression, path, kind(core)})

  defp lower_case(call, [a, b] = branches, path) do
    [{first, x}, {second, y}] = Enum.map(branches, &clause(&1, path))

    if first not in [true, false] or second != not first,
      do: fail({:unsupported_boolean_case, path, [a, b]})

    {:bool_case, call, first, lower(x, path ++ [first]), lower(y, path ++ [second])}
  end

  defp lower_case(call, branches, path) when length(branches) == 3 do
    rows = Enum.map(branches, &clause(&1, path))

    tagged =
      Enum.map(rows, fn
        {{:data, binder}, body} -> {:data, {binder, body}}
        {name, body} when name in [:closed, :timeout] -> {name, body}
        _ -> fail({:unsupported_reply_pattern, path})
      end)

    if Enum.sort(Keyword.keys(tagged)) != [:closed, :data, :timeout],
      do: fail({:unsupported_reply_case, path})

    {binder, data} = Keyword.fetch!(tagged, :data)

    {:reply_case, call, binder, Keyword.keys(tagged), lower(data, path ++ [:data]),
     lower(Keyword.fetch!(tagged, :closed), path ++ [:closed]),
     lower(Keyword.fetch!(tagged, :timeout), path ++ [:timeout])}
  end

  defp lower_case(_call, _branches, path), do: fail({:unsupported_case, path})

  defp clause({:c_clause, _, [pattern], {:c_literal, _, true}, body}, path),
    do: {pattern(pattern, path), body}

  defp clause(_clause, path), do: fail({:unsupported_guard_or_pattern, path})
  defp pattern({:c_literal, _, value}, _path) when is_atom(value), do: value

  defp pattern({:c_tuple, _, [{:c_literal, _, :data}, {:c_var, _, binder}]}, _path),
    do: {:data, variable(binder)}

  defp pattern(_pattern, path), do: fail({:unsupported_pattern, path})

  defp fallback?(
         {:c_clause, annotations, [{:c_var, _, binder}], {:c_literal, _, true},
          {:c_primop, _, {:c_literal, _, :match_fail},
           [{:c_tuple, _, [{:c_literal, _, :case_clause}, {:c_var, _, binder}]}]}}
       ),
       do: :compiler_generated in annotations

  defp fallback?(_clause), do: false

  defp call({:c_call, _, {:c_literal, _, module}, {:c_literal, _, name}, args}, path)
       when is_atom(module) and is_atom(name),
       do: {module, name, Enum.map(args, &arg(&1, path ++ [:argument]))}

  defp call(core, path), do: fail({:unsupported_call, path, kind(core)})

  defp arg({:c_var, _, name}, _path), do: {:var, variable(name)}
  defp arg({:c_literal, _, value}, path), do: {:literal, literal(value, path)}
  defp arg(core, path), do: fail({:unsupported_argument, path, kind(core)})
  defp literal(value, _path) when is_atom(value) or is_integer(value), do: value
  defp literal([], _path), do: []
  defp literal([head | tail], path), do: [literal(head, path) | literal(tail, path)]
  defp literal(value, path), do: fail({:unsupported_literal, path, value})

  defp connect({:let_call, binder, call, body}, %{state: :idle} = ctx, calls, path) do
    registered!(call, :prepare, calls, path)
    if binder == ctx.port, do: fail({:port_binding_overwritten, path})

    {model, proof} =
      connect(body, %{ctx | state: :prepared, request: binder}, calls, path ++ [:body])

    {{:prepare, binder, call, model}, "(.prepare (by decide) (by decide) (by decide) #{proof})"}
  end

  defp connect({:bool_case, call, first, a, b}, %{state: :prepared} = ctx, calls, path) do
    expected =
      {:erlang, :port_command, [{:var, ctx.port}, {:var, ctx.request}, {:literal, [:nosuspend]}]}

    if call != expected, do: fail({:unsupported_submission, path, call})

    {ma, pa} =
      connect(
        a,
        %{ctx | state: if(first, do: :awaiting_response, else: :rejected)},
        calls,
        path ++ [first]
      )

    {mb, pb} =
      connect(
        b,
        %{ctx | state: if(first, do: :rejected, else: :awaiting_response)},
        calls,
        path ++ [not first]
      )

    {{:submit, call, first, ma, mb},
     "(.submit (by decide) (by decide) (by decide) (by decide) #{pa} #{pb})"}
  end

  defp connect(
         {:reply_case, call, binder, _order, a, b, c},
         %{state: :awaiting_response} = ctx,
         calls,
         path
       ) do
    registered!(call, :reply, calls, path)

    if elem(call, 2) != [{:var, ctx.port}] or binder in [ctx.port, ctx.request],
      do: fail({:reply_argument_mismatch, path})

    {ma, pa} =
      connect(a, %{ctx | state: :response_received, data: binder}, calls, path ++ [:data])

    {mb, pb} = connect(b, %{ctx | state: :closed}, calls, path ++ [:closed])
    {mc, pc} = connect(c, %{ctx | state: :timed_out}, calls, path ++ [:timeout])

    {{:reply, call, binder, ma, mb, mc},
     "(.reply (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) #{pa} #{pb} #{pc})"}
  end

  defp connect({:tail_call, call}, %{state: :response_received} = ctx, calls, path) do
    registered!(call, :decode, calls, path)
    if elem(call, 2) != [{:var, ctx.data}], do: fail({:decode_argument_mismatch, path})
    {{:decode, call}, "(.decode (by decide) (by decide) (by decide) (by decide))"}
  end

  defp connect({:ret, arg}, %{state: :rejected}, _calls, _path),
    do:
      {{:ret, arg, [:return_rejection], :failed},
       "(.ret (by decide) (.cons (by decide) .nil) (by decide))"}

  defp connect({:ret, arg}, %{state: state}, _calls, _path) when state in [:closed, :timed_out],
    do: {{:ret, arg, [], state}, "(.ret (by decide) .nil (by decide))"}

  defp connect(source, ctx, _calls, path),
    do: fail({:unsupported_workflow, path, ctx.state, elem(source, 0)})

  defp registered!({m, f, args} = call, role, calls, path) do
    if Map.fetch!(calls, role) != {m, f, length(args)},
      do: fail({:missing_or_mismatched_call_contract, path, role, call})
  end

  defp budget({:ret, _}), do: 1
  defp budget({:let_call, _, {_, _, args}, body}), do: 2 + length(args) + budget(body)
  defp budget({:bool_case, {_, _, args}, _, a, b}), do: 4 + length(args) + budget(a) + budget(b)

  defp budget({:reply_case, {_, _, args}, _, _, a, b, c}),
    do: 9 + length(args) + budget(a) + budget(b) + budget(c)

  defp budget({:tail_call, {_, _, args}}), do: 1 + length(args)

  defp variable(value), do: inspect(value)
  defp kind(core) when is_tuple(core), do: elem(core, 0)
  defp kind(_core), do: :malformed_core
  defp fail(reason), do: throw({:port_source, reason})
end

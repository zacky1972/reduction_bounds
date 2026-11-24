defmodule ReductionBounds.RpcSource do
  @moduledoc """
  Reifies a restricted, helper-contracted RPC client from BEAM debug information.

  The four arguments are server PID, correlation reference, payload and timeout.
  Accepted Core constructs a `{:request, reference, payload}` tuple, sends it
  once with `:erlang.send/2`, branches on a declared reply helper, decodes the
  reply through a declared helper, and returns `:timeout` on the timeout arm.
  Reply and timeout clauses can be reordered; guards must be literal true.

  This is finite normal-execution correspondence under explicit primitive and
  helper contracts. It is not native receive analysis. Helpers' matching,
  scanning, delivery and totality remain obligations. Monitored sessions,
  retries, native receive, dynamic calls, exceptions and unsupported syntax
  report the target and structural source path. No source termination or
  compiler/runtime receive optimization is inferred. Current cost profiles use
  unary integer server contracts, so the request payload must satisfy that
  handler's integer input domain.
  """
  alias ReductionBounds.{RpcCost, RpcTerm, SearchBound}

  @spec infer(ReductionBounds.target(), map(), keyword()) :: {:ok, map()} | {:error, term()}
  def infer(target, profile, options \\ [])

  def infer({m, f, 4} = target, profile, options) when is_atom(m) and is_atom(f) do
    with :ok <- RpcCost.validate(profile),
         {:ok, settings} <- settings(options),
         true <- profile.conditions.session.monitor_id == nil,
         {:ok, core} <- SearchBound.core_function(target, settings.beam_binaries) do
      {:ok, candidate(core, target, profile, settings.calls)}
    else
      false -> {:error, {:rpc_source, target, {:unsupported_monitor, []}}}
      {:error, reason} -> {:error, {:rpc_source, target, reason}}
    end
  catch
    {:rpc_source, reason} -> {:error, {:rpc_source, target, reason}}
  end

  def infer({m, f, arity} = target, _profile, _options)
      when is_atom(m) and is_atom(f) and is_integer(arity) and arity >= 0,
      do: {:error, {:rpc_source, target, {:unsupported_target_arity, [], 4}}}

  def infer(target, _profile, _options),
    do: {:error, {:rpc_source, target, {:invalid_target, []}}}

  defp settings(options) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, beam_binaries: [], calls: %{}),
         true <-
           is_list(options[:beam_binaries]) and Enum.all?(options[:beam_binaries], &is_binary/1),
         :ok <- calls(options[:calls]) do
      {:ok, Map.new(options)}
    else
      false -> {:error, :invalid_rpc_source_options}
      error -> error
    end
  end

  defp calls(%{reply: {rm, rf, 3}, decode: {dm, df, 1}} = calls)
       when is_atom(rm) and is_atom(rf) and is_atom(dm) and is_atom(df) and rm != :erlang and
              dm != :erlang do
    if map_size(calls) == 2 and {rm, rf} != {dm, df},
      do: :ok,
      else: {:error, :ambiguous_rpc_source_contracts}
  end

  defp calls(_calls), do: {:error, {:required_rpc_source_contracts, [reply: 3, decode: 1]}}

  defp candidate({:c_fun, _, vars, body}, target, profile, calls) do
    names = Enum.map(vars, fn {:c_var, _, name} -> variable(name) end)
    if length(Enum.uniq(names)) != 4, do: fail({:invalid_argument_bindings, []})
    [server, token, input, timeout] = names

    ctx = %{
      state: :idle,
      server: server,
      token: token,
      input: input,
      timeout: timeout,
      request: "",
      data: ""
    }

    source = lower(body, [])
    expected_timeout = timeout_value(profile.conditions.mailbox.timeout)
    {program, certificate} = connect(source, ctx, calls, expected_timeout, [])

    %{
      source: :rpc_source,
      target: target,
      cost_profile: profile,
      conditions: profile.conditions,
      core_source: source,
      program: program,
      connection: certificate,
      context: ctx,
      timeout_value: expected_timeout,
      source_node_bound: budget(source),
      calls: calls,
      source_correspondence: :certificate_pending,
      lean_status: :not_checked,
      proof_scope: :finite_normal_reified_core_under_rpc_helper_contracts,
      primitive_contracts: [
        %{
          target: {:erlang, :send, 2},
          status: :assumed,
          result: :sent_term,
          delivery: :not_established,
          totality: :not_established
        }
      ],
      call_contracts:
        Map.new(calls, fn {role, mfa} ->
          {role,
           %{
             target: mfa,
             status: :assumed,
             totality: :not_established,
             result_and_trace_contract: role
           }}
        end),
      trusted: [:beam_debug_extraction, :core_reification, :term_abstraction, :serialization],
      unverified: [
        :helper_implementations,
        :input_applicability,
        :mailbox_trace_association,
        :response_payload_association,
        :helper_matching_and_scanning,
        :reply_provenance,
        :helper_totality,
        :exceptions,
        :unfinished_source_prefixes,
        :source_termination,
        :runtime_correspondence,
        :wall_clock_time
      ]
    }
  end

  defp lower({:c_let, _, [{:c_var, _, binder}], value, body}, path),
    do:
      {:let_value, variable(binder), arg(value, path ++ [:binding]), lower(body, path ++ [:body])}

  defp lower({:c_seq, _, call, body}, path),
    do: {:seq_call, call(call, path ++ [:call]), lower(body, path ++ [:body])}

  defp lower({:c_case, _, subject, clauses}, path) do
    {branches, [fallback]} = Enum.split(clauses, -1)
    if not fallback?(fallback), do: fail({:unsupported_case_fallback, path})
    rows = Enum.map(branches, &clause(&1, path))
    if length(rows) != 2, do: fail({:unsupported_reply_case, path})

    {{:reply, binder}, reply_body} =
      Enum.find(rows, fn {p, _} -> match?({:reply, _}, p) end) ||
        fail({:missing_reply_clause, path})

    {:timeout, timeout_body} =
      Enum.find(rows, fn {p, _} -> p == :timeout end) || fail({:missing_timeout_clause, path})

    order =
      Enum.map(rows, fn
        {{:reply, _}, _} -> :reply
        {:timeout, _} -> :timeout
      end)

    {:reply_case, call(subject, path ++ [:subject]), binder, order,
     lower(reply_body, path ++ [:reply]), lower(timeout_body, path ++ [:timeout])}
  end

  defp lower({:c_call, _, _, _, _} = call, path), do: {:tail_call, call(call, path)}
  defp lower({:c_literal, _, _} = value, path), do: {:ret, arg(value, path)}
  defp lower({:c_var, _, _} = value, path), do: {:ret, arg(value, path)}
  defp lower(core, path), do: fail({:unsupported_expression, path, kind(core)})

  defp clause({:c_clause, _, [pattern], {:c_literal, _, true}, body}, path),
    do: {pattern(pattern, path), body}

  defp clause(_clause, path), do: fail({:unsupported_guard_or_pattern, path})

  defp pattern({:c_tuple, _, [{:c_literal, _, :reply}, {:c_var, _, binder}]}, _path),
    do: {:reply, variable(binder)}

  defp pattern({:c_literal, _, :timeout}, _path), do: :timeout
  defp pattern(_pattern, path), do: fail({:unsupported_pattern, path})

  defp fallback?(
         {:c_clause, annotations, [{:c_var, _, binder}], {:c_literal, _, true},
          {:c_primop, _, {:c_literal, _, :match_fail},
           [{:c_tuple, _, [{:c_literal, _, :case_clause}, {:c_var, _, binder}]}]}}
       ),
       do: :compiler_generated in annotations

  defp fallback?(_clause), do: false

  defp call({:c_call, _, {:c_literal, _, m}, {:c_literal, _, f}, args}, path)
       when is_atom(m) and is_atom(f),
       do: {m, f, Enum.map(args, &arg(&1, path ++ [:argument]))}

  defp call(core, path), do: fail({:unsupported_call, path, kind(core)})
  defp arg({:c_var, _, name}, _path), do: {:var, variable(name)}

  defp arg({:c_tuple, _, [a, b, c]}, path),
    do: {:tuple3, arg(a, path), arg(b, path), arg(c, path)}

  defp arg({:c_literal, _, value}, path) do
    case RpcTerm.from_term(value) do
      {:ok, term} -> {:literal, term}
      _ -> fail({:unsupported_literal, path})
    end
  end

  defp arg(core, path), do: fail({:unsupported_argument, path, kind(core)})

  defp connect({:let_value, binder, value, body}, %{state: :idle} = c, calls, timeout, path) do
    expected = {:tuple3, {:literal, {:atom, "request"}}, {:var, c.token}, {:var, c.input}}

    if value != expected or binder in protected(c),
      do: fail({:request_construction_mismatch, path})

    {p, proof} =
      connect(body, %{c | state: :prepared, request: binder}, calls, timeout, path ++ [:body])

    {{:prepare, binder, value, p},
     "(.prepare (by decide) (by decide) (by decide) (by decide) #{proof})"}
  end

  defp connect({:seq_call, call, body}, %{state: :prepared} = c, calls, timeout, path) do
    if call != {:erlang, :send, [{:var, c.server}, {:var, c.request}]},
      do: fail({:send_argument_mismatch, path})

    {p, proof} = connect(body, %{c | state: :awaiting_request}, calls, timeout, path ++ [:body])
    {{:send, call, p}, "(.send (by decide) (by decide) (by decide) #{proof})"}
  end

  defp connect(
         {:reply_case, call, binder, _order, a, b},
         %{state: :awaiting_request} = c,
         calls,
         timeout,
         path
       ) do
    registered!(call, :reply, calls, path)
    {_, _, args} = call
    allowed_timeout = [{:var, c.timeout}, {:literal, timeout}]

    if length(args) != 3 or Enum.take(args, 2) != [{:var, c.server}, {:var, c.token}] or
         List.last(args) not in allowed_timeout or binder in [c.request | protected(c)],
       do: fail({:reply_argument_mismatch, path})

    {pa, ca} =
      connect(a, %{c | state: :reply_received, data: binder}, calls, timeout, path ++ [:reply])

    {pb, cb} = connect(b, %{c | state: :timeout_observed}, calls, timeout, path ++ [:timeout])

    {{:reply, call, binder, pa, pb},
     "(.reply (by decide) (by decide) (by decide) (by decide) (by decide) #{ca} #{cb})"}
  end

  defp connect({:tail_call, call}, %{state: :reply_received} = c, calls, _timeout, path) do
    registered!(call, :decode, calls, path)
    if elem(call, 2) != [{:var, c.data}], do: fail({:decode_argument_mismatch, path})
    {{:decode, call}, "(.decode (by decide) (by decide) (by decide))"}
  end

  defp connect(
         {:ret, {:literal, {:atom, "timeout"}}} = core,
         %{state: :timeout_observed},
         _calls,
         _timeout,
         _path
       ),
       do: {{:timeout, elem(core, 1)}, "(.timeout (by decide) (by decide))"}

  defp connect(source, c, _calls, _timeout, path),
    do: fail({:unsupported_workflow, path, c.state, elem(source, 0)})

  defp registered!({m, f, args}, role, calls, path) do
    if calls[role] != {m, f, length(args)}, do: fail({:mismatched_helper_contract, path, role})
  end

  defp protected(c), do: [c.server, c.token, c.input, c.timeout]
  defp budget({:let_value, _, value, body}), do: 2 + arg_budget(value) + budget(body)
  defp budget({:seq_call, {_, _, args}, body}), do: 1 + length(args) + budget(body)

  defp budget({:reply_case, {_, _, args}, _, _, a, b}),
    do: 6 + length(args) + budget(a) + budget(b)

  defp budget({:tail_call, {_, _, args}}), do: 1 + length(args)
  defp budget({:ret, _}), do: 1
  defp arg_budget({:tuple3, a, b, c}), do: 1 + arg_budget(a) + arg_budget(b) + arg_budget(c)
  defp arg_budget(_arg), do: 1
  defp timeout_value(:infinity), do: {:atom, "infinity"}
  defp timeout_value(n), do: {:integer, n}
  defp variable(name), do: inspect(name)
  defp kind(core) when is_tuple(core), do: elem(core, 0)
  defp kind(_core), do: :malformed_core
  defp fail(reason), do: throw({:rpc_source, reason})
end

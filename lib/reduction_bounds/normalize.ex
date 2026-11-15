defmodule ReductionBounds.Normalize do
  @moduledoc false

  alias ReductionBounds.CoreFragment

  @type fact :: {CoreFragment.name(), CoreFragment.name()}
  @type certificate :: %{
          path: [atom()],
          facts: [fact()],
          original: CoreFragment.expr(),
          normalized: CoreFragment.expr(),
          rewrite:
            {:read_field, CoreFragment.name(), CoreFragment.name(), CoreFragment.name(),
             CoreFragment.expr()}
        }

  @spec normalize(CoreFragment.t(), [fact()]) ::
          %{program: CoreFragment.t(), certificates: [certificate()]}
  def normalize(%{expression: expression} = program, assumptions \\ []) do
    {expression, certificates} = visit(expression, MapSet.new(assumptions), [])

    %{program: %{program | expression: expression}, certificates: certificates}
  end

  defp visit(
         {:case_map, {:var, subject}, %{tag: nil, fields: [{key, binder}]}, {:var, binder},
          fallback} = original,
         facts,
         path
       ) do
    if MapSet.member?(facts, {subject, key}) do
      normalized = {:field, {:var, subject}, key}

      certificate = %{
        path: Enum.reverse(path),
        facts: Enum.sort(facts),
        original: original,
        normalized: normalized,
        rewrite: {:read_field, subject, key, binder, fallback}
      }

      {normalized, [certificate]}
    else
      visit_case(original, facts, path)
    end
  end

  defp visit({:case_map, _, _, _, _} = expression, facts, path),
    do: visit_case(expression, facts, path)

  defp visit({:case_map_guarded, subject, pattern, condition, matched, fallback}, facts, path) do
    matched_facts = matched_facts(subject, pattern, facts)
    {subject, subject_proofs} = visit(subject, facts, [:subject | path])
    {condition, condition_proofs} = visit(condition, matched_facts, [:condition | path])
    {matched, matched_proofs} = visit(matched, matched_facts, [:matched | path])
    {fallback, fallback_proofs} = visit(fallback, facts, [:fallback | path])

    {{:case_map_guarded, subject, pattern, condition, matched, fallback},
     subject_proofs ++ condition_proofs ++ matched_proofs ++ fallback_proofs}
  end

  defp visit({:let_in, name, rhs, body}, facts, path) do
    body_facts = transfer_facts(facts, name, rhs)
    {rhs, rhs_proofs} = visit(rhs, facts, [:rhs | path])
    {body, body_proofs} = visit(body, body_facts, [:body | path])
    {{:let_in, name, rhs, body}, rhs_proofs ++ body_proofs}
  end

  defp visit({:guarded, condition, success, failure}, facts, path) do
    {condition, condition_proofs} = visit(condition, facts, [:condition | path])
    {success, success_proofs} = visit(success, facts, [:success | path])
    {failure, failure_proofs} = visit(failure, facts, [:failure | path])

    {{:guarded, condition, success, failure},
     condition_proofs ++ success_proofs ++ failure_proofs}
  end

  defp visit({:field, subject, key}, facts, path) do
    {subject, proofs} = visit(subject, facts, [:subject | path])
    {{:field, subject, key}, proofs}
  end

  defp visit({operation, operand}, facts, path) when operation in [:is_integer, :is_map] do
    {operand, proofs} = visit(operand, facts, [:operand | path])
    {{operation, operand}, proofs}
  end

  defp visit({:update, subject, key, rhs}, facts, path) do
    {subject, subject_proofs} = visit(subject, facts, [:subject | path])
    {rhs, rhs_proofs} = visit(rhs, facts, [:rhs | path])
    {{:update, subject, key, rhs}, subject_proofs ++ rhs_proofs}
  end

  defp visit({operation, left, right}, facts, path) when operation in [:ge, :sub] do
    {left, left_proofs} = visit(left, facts, [:left | path])
    {right, right_proofs} = visit(right, facts, [:right | path])
    {{operation, left, right}, left_proofs ++ right_proofs}
  end

  defp visit(expression, _facts, _path), do: {expression, []}

  defp visit_case({:case_map, subject, pattern, matched, fallback}, facts, path) do
    matched_facts = matched_facts(subject, pattern, facts)
    {subject, subject_proofs} = visit(subject, facts, [:subject | path])
    {matched, matched_proofs} = visit(matched, matched_facts, [:matched | path])
    {fallback, fallback_proofs} = visit(fallback, facts, [:fallback | path])

    {{:case_map, subject, pattern, matched, fallback},
     subject_proofs ++ matched_proofs ++ fallback_proofs}
  end

  defp matched_facts(subject, pattern, facts) do
    names = MapSet.new(pattern.fields, &elem(&1, 1))
    remaining = forget(facts, names)
    learn(subject, pattern, names, remaining)
  end

  defp learn({:var, subject}, pattern, names, facts) do
    if MapSet.member?(names, subject) do
      facts
    else
      keys = Enum.map(pattern.fields, &elem(&1, 0))
      keys = if pattern.tag, do: ["__struct__" | keys], else: keys
      Enum.reduce(keys, facts, &MapSet.put(&2, {subject, &1}))
    end
  end

  defp learn(_subject, _pattern, _names, facts), do: facts

  defp transfer_facts(facts, target, rhs) do
    remaining = forget(facts, MapSet.new([target]))

    case rhs do
      {:var, source} ->
        Enum.reduce(facts, remaining, fn
          {^source, key}, acc -> MapSet.put(acc, {target, key})
          _fact, acc -> acc
        end)

      _ ->
        remaining
    end
  end

  defp forget(facts, names), do: MapSet.reject(facts, &MapSet.member?(names, elem(&1, 0)))
end

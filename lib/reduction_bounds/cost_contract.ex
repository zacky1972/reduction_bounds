defmodule ReductionBounds.CostContract do
  @moduledoc """
  Declares operation costs and their applicability for the integer cost fragment.

  An operation cost contract is distinct from a callee's `call_contracts` entry.
  It identifies a cost unit and the modeled semantics and charge events. Cost
  functions take two natural parameters whose meanings depend on the operation.
  For arithmetic they are magnitude widths; for shifts and masks the second
  parameter is the constant shift amount or mask width. Local fixed charges
  use two unused parameters, both zero.

  Functions are either symbolic, or declarative expressions built from natural
  constants, `:left`, `:right`, and `{:add, a, b}`, `{:mul, a, b}`, or
  `{:max, a, b}`. Every declared operation needs a function when expressions
  are supplied. Auxiliary cost names in callee budgets need their own parameter
  declarations. Elixir functions and arbitrary Lean source are not expressions.

  This module validates declarations and evaluates expressions. Use
  `ReductionBounds.compare_cost_contracts/3` for separate Lean checks of
  declarative function monotonicity, pointwise ordering, and budget ordering.
  The comparison also checks a conditional execution-cost theorem under
  explicit callee assumptions. It does not select a target or transfer a bound.
  Use `ReductionBounds.transfer_integer_bound/3` to recheck a target and its
  original bound, instantiate concrete contracts, and apply the ordering.
  Neither API establishes applicability to a concrete VM implementation.
  Integer inference continues to check a bound quantified
  over arbitrary nondecreasing cost functions. A supplied declaration is reported
  separately with `contract_instantiation: :not_checked`; evaluating an expression
  in Elixir is not a Lean certificate for that instance.

  ## Examples

      iex> alias ReductionBounds.CostContract
      iex> {:ok, contract} = CostContract.new(id: :analysis)
      iex> contract.functions
      :symbolic
      iex> CostContract.evaluate(contract, :addition, [8, 8])
      {:error, {:unresolved_cost_function, :addition}}

      iex> alias ReductionBounds.CostContract
      iex> expr = {:add, 1, {:mul, :left, :right}}
      iex> functions = Map.new(CostContract.operations(), &{&1, expr})
      iex> {:ok, contract} = CostContract.new(id: :example, functions: functions)
      iex> CostContract.evaluate(contract, :multiplication, [8, 9])
      {:ok, 73}

  Names such as `:jit` are labels only. A successful declaration does not mean
  that a VM implementation satisfies it, or that its unit is ERTS reductions.
  """

  @execution_operations [
    :value,
    :variable,
    :binding,
    :comparison,
    :recursive_call,
    :addition,
    :subtraction,
    :multiplication,
    :xor,
    :shift_left,
    :shift_right,
    :mask,
    :static_call
  ]

  @local {:unused, :unused}
  @widths {:left_magnitude_bits, :right_magnitude_bits}
  @parameters %{
    value: @local,
    variable: @local,
    binding: @local,
    comparison: @widths,
    recursive_call: @local,
    addition: @widths,
    subtraction: @widths,
    multiplication: @widths,
    xor: @widths,
    shift_left: {:input_magnitude_bits, :shift_amount},
    shift_right: {:input_magnitude_bits, :shift_amount},
    mask: {:input_magnitude_bits, :mask_width},
    static_call: @local
  }

  @typedoc "An expression denoting a natural-valued operation cost."
  @type expression ::
          non_neg_integer()
          | :left
          | :right
          | {:add | :mul | :max, expression(), expression()}

  @type label :: atom() | String.t()
  @type parameter_names :: {atom(), atom()}
  @type t :: %__MODULE__{
          id: label(),
          cost_unit: label(),
          semantics: :core_integer_v1,
          events: :integer_cost_v1,
          parameter_domain: :all_natural_pairs,
          auxiliary_parameters: %{optional(atom()) => parameter_names()},
          functions: :symbolic | %{optional(atom()) => expression()}
        }

  defstruct id: :symbolic_integer,
            cost_unit: :symbolic_work,
            semantics: :core_integer_v1,
            events: :integer_cost_v1,
            parameter_domain: :all_natural_pairs,
            auxiliary_parameters: %{},
            functions: :symbolic

  @doc "Builds a validated declaration for the supported integer cost profile."
  @spec new(keyword()) :: {:ok, t()} | {:error, term()}
  def new(options \\ []) do
    keys = [:id, :cost_unit, :functions, :auxiliary_parameters]

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, keys) do
      contract = struct!(__MODULE__, options)

      case validate(contract) do
        :ok -> {:ok, contract}
        error -> error
      end
    else
      _ -> {:error, :invalid_contract_options}
    end
  end

  @doc "Operation names in the numeric order used by the integer execution semantics."
  @spec execution_operations() :: [atom()]
  def execution_operations(), do: @execution_operations

  @doc "Returns the names of the built-in cost events."
  @spec operations() :: [atom()]
  def operations(), do: @parameters |> Map.keys() |> Enum.sort()

  @doc "Returns the meanings of both parameters for every declared cost event."
  @spec parameters(t()) :: %{atom() => parameter_names()}
  def parameters(%__MODULE__{} = contract),
    do: Map.merge(@parameters, contract.auxiliary_parameters)

  @doc "Validates a declaration, including structs constructed without new/1."
  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%__MODULE__{} = contract) do
    with :ok <- check(label?(contract.id), {:invalid_contract_id, contract.id}),
         :ok <- check(label?(contract.cost_unit), {:invalid_cost_unit, contract.cost_unit}),
         :ok <- validate_profile(contract),
         :ok <- validate_auxiliary(contract.auxiliary_parameters) do
      validate_functions(contract.functions, parameters(contract))
    end
  end

  def validate(value), do: {:error, {:invalid_cost_contract, value}}

  @doc false
  @spec prepare(term(), [atom()]) :: {:ok, t()} | {:error, term()}
  def prepare(nil, names) do
    extra = names -- operations()
    auxiliary = Map.new(extra, &{&1, {:callee_parameter_1, :callee_parameter_2}})
    new(auxiliary_parameters: auxiliary)
  end

  def prepare(contract, names) do
    with :ok <- validate(contract),
         [] <- names -- Map.keys(parameters(contract)) do
      {:ok, contract}
    else
      [_ | _] = missing -> {:error, {:undeclared_cost_operations, Enum.sort(missing)}}
      error -> error
    end
  end

  @doc "Evaluates a declared function; this does not produce proof evidence."
  @spec evaluate(t(), atom(), [non_neg_integer()]) ::
          {:ok, non_neg_integer()} | {:error, term()}
  def evaluate(contract, operation, [left, right])
      when is_atom(operation) and is_integer(left) and left >= 0 and
             is_integer(right) and right >= 0 do
    with :ok <- validate(contract),
         :ok <- require_operation(contract, operation) do
      evaluate_function(contract.functions, operation, left, right)
    end
  end

  def evaluate(_contract, _operation, args), do: {:error, {:invalid_cost_arguments, args}}

  defp require_operation(contract, operation) do
    check(Map.has_key?(parameters(contract), operation), {:unknown_operation, operation})
  end

  defp validate_profile(contract) do
    profile = {contract.semantics, contract.events, contract.parameter_domain}

    check(
      profile == {:core_integer_v1, :integer_cost_v1, :all_natural_pairs},
      {:unsupported_cost_profile, profile}
    )
  end

  defp validate_auxiliary(parameters) when is_map(parameters) and not is_struct(parameters) do
    case Enum.find(parameters, fn {name, pair} -> not auxiliary?(name, pair) end) do
      nil -> :ok
      entry -> {:error, {:invalid_auxiliary_parameters, entry}}
    end
  end

  defp validate_auxiliary(value), do: {:error, {:invalid_auxiliary_parameters, value}}

  defp auxiliary?(name, {left, right}) do
    is_atom(name) and name not in [nil, true, false] and
      not Map.has_key?(@parameters, name) and is_atom(left) and is_atom(right) and
      label?(left) and label?(right)
  end

  defp auxiliary?(_name, _pair), do: false

  defp validate_functions(:symbolic, _parameters), do: :ok

  defp validate_functions(functions, parameters)
       when is_map(functions) and not is_struct(functions) do
    if Enum.sort(Map.keys(functions)) == Enum.sort(Map.keys(parameters)) do
      validate_definitions(functions)
    else
      {:error, :cost_function_registry_mismatch}
    end
  end

  defp validate_functions(value, _parameters), do: {:error, {:invalid_cost_functions, value}}

  defp validate_definitions(functions) do
    case Enum.find(functions, fn {_name, expr} -> not expression?(expr) end) do
      nil -> :ok
      {name, expr} -> {:error, {:invalid_cost_function, name, expr}}
    end
  end

  defp expression?(value) when is_integer(value), do: value >= 0
  defp expression?(value) when value in [:left, :right], do: true

  defp expression?({op, left, right}) when op in [:add, :mul, :max],
    do: expression?(left) and expression?(right)

  defp expression?(_value), do: false

  defp evaluate_function(:symbolic, operation, _left, _right),
    do: {:error, {:unresolved_cost_function, operation}}

  defp evaluate_function(functions, operation, left, right),
    do: {:ok, eval(Map.fetch!(functions, operation), left, right)}

  defp eval(value, _left, _right) when is_integer(value), do: value
  defp eval(:left, left, _right), do: left
  defp eval(:right, _left, right), do: right
  defp eval({:add, a, b}, left, right), do: eval(a, left, right) + eval(b, left, right)
  defp eval({:mul, a, b}, left, right), do: eval(a, left, right) * eval(b, left, right)
  defp eval({:max, a, b}, left, right), do: max(eval(a, left, right), eval(b, left, right))

  defp label?(value) when is_atom(value), do: value not in [nil, true, false]
  defp label?(value) when is_binary(value), do: String.trim(value) != ""
  defp label?(_value), do: false

  defp check(true, _reason), do: :ok
  defp check(false, reason), do: {:error, reason}
end

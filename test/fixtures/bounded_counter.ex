defmodule ReductionBounds.Fixtures.BoundedCounter do
  @moduledoc false
  @compile :debug_info

  defstruct balance: 0, limit: 0

  def debit(%__MODULE__{balance: balance} = counter, amount)
      when is_integer(amount) and amount >= 0 and balance >= amount do
    %{counter | balance: balance - amount}
  end

  def debit(%__MODULE__{} = counter, _amount), do: counter

  def set_limit(%__MODULE__{limit: _} = counter, limit) when is_integer(limit) do
    %{counter | limit: limit}
  end

  def set_limit(%__MODULE__{} = counter, _limit), do: counter

  def read_checked(%__MODULE__{balance: _} = counter), do: counter.balance
  def read_unchecked(counter), do: counter.balance
end

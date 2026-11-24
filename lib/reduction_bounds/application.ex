defmodule ReductionBounds.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    Supervisor.start_link([ReductionBounds.ProofPreparation],
      strategy: :one_for_one,
      name: ReductionBounds.Supervisor
    )
  end
end

defmodule ReductionBounds.Benchmark.Workspace do
  @moduledoc false

  @doc false
  @spec copy_priv!(Path.t(), Path.t()) :: :ok
  def copy_priv!(build, source \\ Path.expand("priv")) do
    # Relative links through temporary-directory aliases (for example /var on
    # macOS) may resolve against a different physical parent directory. Keep a
    # real copy in the isolated application before any measured child runs.
    destination = Path.join([build, "lib", "reduction_bounds", "priv"])

    case File.read_link(destination) do
      {:ok, _target} -> File.rm!(destination)
      {:error, _reason} -> :ok
    end

    File.mkdir_p!(Path.dirname(destination))
    File.cp_r!(source, destination)
    :ok
  end
end

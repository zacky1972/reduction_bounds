defmodule ReductionBounds.MixProject do
  use Mix.Project

  def project do
    [
      app: :reduction_bounds,
      version: "0.1.0",
      elixir: "~> 1.20",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      name: "Reduction bounds",
      description: "TODO: write a proper description",
      docs: docs(),
      package: package(),
      aliases: aliases(),
      dialyzer: dialyzer(),
      test_ignore_filters: [&String.starts_with?(&1, "test/fixtures/")]
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      mod: {ReductionBounds.Application, []},
      extra_applications: [:logger]
    ]
  end

  def docs do
    [
      main: "readme",
      assets: %{"docs/baselines" => "."},
      extras: [
        "README.md",
        "docs/examples.md",
        "docs/examples/verification.md",
        "docs/examples/cost_contracts.md",
        "docs/examples/list_bounds.md",
        "docs/examples/ports.md",
        "docs/proof.md",
        "docs/roadmap.md",
        "docs/toolchains.md",
        "docs/benchmarking.md",
        "docs/shared_proofs.md",
        "docs/baselines/issue8-linux-otp29.md",
        "docs/baselines/issue8-integer-cache.md",
        "docs/baselines/issue8-all-proofs.md",
        "LICENSE.md"
      ]
    ]
  end

  def package do
    [
      name: :reduction_bounds,
      licenses: ["Apache-2.0"],
      links: %{"GitHub" => "https://github.com/TODO/reduction_bounds"}
    ]
  end

  def aliases do
    [
      check: [
        "hex.audit",
        "compile --warnings-as-errors --force",
        "format --check-formatted",
        "credo --strict",
        "deps.unlock --check-unused",
        "spellweaver.check",
        "dialyzer"
      ],
      precommit: [
        "hex.audit",
        "compile --warnings-as-errors --force",
        "format",
        "credo --strict",
        "deps.unlock --unused",
        "spellweaver.check",
        "dialyzer",
        "test"
      ]
    ]
  end

  def cli do
    [
      preferred_envs: [precommit: :test, "reduction_bounds.bench": :test]
    ]
  end

  def dialyzer do
    [
      plt_add_apps: [:mix],
      ignore_warnings: ".dialyzer_ignore.exs"
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:nstandard, "~> 0.5", runtime: false},
      {:ex_doc, "~> 0.40", only: [:dev, :test], runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:spellweaver, "~> 0.1.8", only: [:dev, :test], runtime: false},
      {:lynx, git: "https://github.com/josevalim/lynx.git"},
      {:circular_buffer,
       git: "https://github.com/elixir-toniq/circular_buffer.git", tag: "v1.1.0", only: :test}
    ]
  end
end

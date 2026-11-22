# Maintaining Lean and Lynx toolchains

Lynx's fetched `lean-toolchain` file specifies the required Lean version.
Updating Elan and installing a Lean toolchain are separate operations.

## Updating Elan

If Elan was installed with the official installer:

```sh
elan self update
elan --version
```

For a package-manager installation, update through that package manager.
See the [Elan toolchain documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/).

## Updating Lynx and its Lean toolchain

When you choose to update Lynx, run the following commands from your
project's root. Re-read `lean-toolchain` after updating the dependency,
because the required Lean version may have changed.

```sh
mix deps.update lynx
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lean --version
lake --version
mix compile
mix test
```

Review and commit the resulting `mix.lock` changes after checking
compatibility with your project. Installing a newer Lean toolchain alone
does not update Lynx or verify compatibility with ReductionBounds.

## Working in this repository

The tracked `lean-toolchain` file selects the project toolchain when
`ELAN_TOOLCHAIN` is unset. After fetching dependencies, check that it agrees
with Lynx:

```sh
cmp lean-toolchain deps/lynx/lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
```

When intentionally updating Lynx in this repository, synchronize the
tracked toolchain file after checking compatibility, and commit it with
the corresponding lockfile change. The environment-variable commands
above remain useful in consuming projects without a matching project
file, and an explicit `ELAN_TOOLCHAIN` takes precedence over that file.

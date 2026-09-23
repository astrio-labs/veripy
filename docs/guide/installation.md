# Installation

VeriPy is experimental research software. Install from the repository. The package named `veripy` on PyPI is unrelated.

## Install Python dependencies

Use Python 3.11 or newer. Python 3.12.2 matches the retained research environment. These commands assume a POSIX shell on Linux or macOS.

```sh
git clone https://github.com/astrio-labs/veripy.git
cd veripy
python -m venv .venv
source .venv/bin/activate
python -m pip install -e '.[dev]'
veripy --help
```

On Windows, activate the environment with `.venv\Scripts\Activate.ps1` in PowerShell. Adapt shell commands accordingly. The CI environments provide the tested setup, rather than a claim of complete platform parity.

## Install a prover

Start with Dafny, the default backend. Install the [.NET 8 SDK](https://dotnet.microsoft.com/en-us/download/dotnet/8.0), then run

```sh
dotnet tool install --global dafny --version 4.11.0
export PATH="$HOME/.dotnet/tools:$PATH"
dafny --version
```

If Dafny is already installed, inspect its version before modifying that environment. Installing the Python package does not install either prover.

For Lean, install [elan](https://github.com/leanprover/elan#installation), then use the pinned toolchain from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.33.1
lean --version
```

The repository's `lean-toolchain` selects the version. No mathlib installation is needed for VeriPy's maintained Lean backend.

## Confirm the setup

```sh
python --version
basedpyright --version
veripy --help
```

Continue to [your first proof](first-proof.md). The [Dafny](../DAFNY.md) and [Lean](../LEAN.md) references explain backend-specific requirements. Exact research reproduction also pins Python, Unicode tables, and integer conversion limits.

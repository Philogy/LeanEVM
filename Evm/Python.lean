/--
Python interpreter for the helper scripts in `Evm/EllipticCurvesPy/` —
the repo-local uv venv, never the system python (see CLAUDE.md).
-/
def pythonExe : String := ".venv/bin/python3"

/--
Native helper binary replacing the python scripts on all conform-suite hot
paths (`tools/evmrs`, built by the `evmrs` lakefile target via cargo).
-/
def evmrsExe : String := "tools/evmrs/target/release/evmrs"

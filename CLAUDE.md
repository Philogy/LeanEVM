# LeanEVM

Executable Lean 4 specification of the EVM, tested against the Ethereum
BlockchainTests fixtures (`lake exe conform <threads>`).

## Python

**Always and only use `uv` for anything python.** Never `pip install` into the
system or user site-packages, never `--break-system-packages`.

The conform suite shells out to helper scripts in `EvmYul/EllipticCurvesPy/`
(ECDSA recovery, state trie root, some precompiles). They run via the
repo-local venv at `.venv` (see `pythonExe` in `EvmYul/CachedPython.lean`).
Set it up with:

```sh
uv venv .venv
uv pip install --python .venv/bin/python3 coincurve pycryptodome typing-extensions
```

## Conform suite notes

- Python results are memoised on disk under `.pycache/` (keyed by script +
  arguments) — reruns over the same fixtures skip python entirely. Delete
  `.pycache/` to force recomputation.
- `nproc` does not exist on macOS; always pass an explicit thread count:
  `lake exe conform 8`.
- Per-test results land in `tests_0.txt`; expected failures are listed in
  `Conform/Main.lean`.

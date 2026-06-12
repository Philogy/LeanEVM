# LeanEVM

Executable Lean 4 specification of the EVM, tested against the Ethereum
BlockchainTests fixtures (`lake exe conform <threads>`).

## Python

**Always and only use `uv` for anything python.** Never `pip install` into the
system or user site-packages, never `--break-system-packages`.

The conform suite shells out to helper scripts in `EvmYul/EllipticCurvesPy/`
(rare precompiles, plus fallback paths for ECDSA recovery and trie roots).
They run via the repo-local venv at `.venv` (see `pythonExe` in
`EvmYul/Python.lean`). Set it up with:

```sh
uv venv .venv
uv pip install --python .venv/bin/python3 \
  coincurve pycryptodome typing-extensions eth-typing py_ecc
```

## Conform suite notes

- `nproc` does not exist on macOS; always pass an explicit thread count:
  `lake exe conform 8`.
- A second CLI arg substring-filters fixture file paths for quick samples:
  `lake exe conform 8 stMemoryTest`. Use small samples while iterating —
  the full suite is for phase gates only.
- Per-test results land in `tests_0.txt`; expected failures are listed in
  `Conform/Main.lean`.

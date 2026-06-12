import EvmYul.Wheels
import EvmYul.FFI.ffi

/-!
Disk cache for the python helper scripts (`EvmYul/EllipticCurvesPy/`).

Python interpreter startup dominates the conform-suite runtime. All helper
invocations are deterministic functions of their input, so results are
memoised on disk under `.pycache/<keccak-of-input>`. Repeated conform runs
over the same fixtures then skip python entirely.
-/

/-- Python interpreter for the helper scripts — repo-local uv venv, never the system python (see CLAUDE.md). -/
def pythonExe : String := ".venv/bin/python3"

/-- Run `compute` and memoise its result on disk, keyed by `key`'s keccak hash. -/
def cachedPythonResult (key : String) (compute : IO String) : IO String := do
  let dir : System.FilePath := ".pycache"
  let file := dir / EvmYul.toHex (ffi.KEC key.toUTF8)
  if ← file.pathExists then
    IO.FS.readFile file
  else
    let out ← compute
    IO.FS.createDirAll dir
    -- write-then-rename so concurrent test threads never observe a partial entry
    let tmp : System.FilePath := file.toString ++ s!".{← IO.monoNanosNow}.tmp"
    IO.FS.writeFile tmp out
    IO.FS.rename tmp file
    pure out

/-- `IO.Process.run`, memoised on disk by argument list (script path + inputs). -/
def cachedPythonRun (args : IO.Process.SpawnArgs) : IO String :=
  cachedPythonResult (String.intercalate " " args.args.toList) (IO.Process.run args)

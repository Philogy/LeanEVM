import EvmYul.Wheels
import EvmYul.PerformIO
import EvmYul.CachedPython
import Conform.Wheels

def blobSNARKV (data : String) : String :=
  totallySafePerformIO ∘ cachedPythonRun <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["EvmYul/EllipticCurvesPy/snarkv.py", data]
  }

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s

import EvmYul.Wheels
import EvmYul.PerformIO
import EvmYul.CachedPython
import Conform.Wheels

def blobPointEval (data : String) : String :=
  totallySafePerformIO ∘ cachedPythonRun <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["EvmYul/EllipticCurvesPy/point_evaluation.py", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s

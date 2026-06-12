import EvmYul.PerformIO
import EvmYul.CachedPython
import EvmYul.Wheels
import Conform.Wheels

def blobSHA256 (d : String) : String :=
  totallySafePerformIO ∘ cachedPythonRun <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["EvmYul/EllipticCurvesPy/sha256.py", d]
  }

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)

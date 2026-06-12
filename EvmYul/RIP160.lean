import EvmYul.PerformIO
import EvmYul.CachedPython
import EvmYul.Wheels
import Conform.Wheels

def blobRIP160 (d : String) : String :=
  totallySafePerformIO ∘ cachedPythonRun <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["EvmYul/EllipticCurvesPy/rip160.py", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobRIP160 (toHex d)

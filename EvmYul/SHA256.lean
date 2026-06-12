import EvmYul.PerformIO
import EvmYul.Python
import EvmYul.Wheels
import Conform.Wheels

def blobSHA256 (d : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["EvmYul/EllipticCurvesPy/sha256.py", d]
  }

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)

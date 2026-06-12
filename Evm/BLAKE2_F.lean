import Evm.Wheels
import Evm.PerformIO
import Evm.Python
import Conform.Wheels

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := pythonExe,
    args := #["Evm/EllipticCurvesPy/blake2_f.py", data]
  }

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s

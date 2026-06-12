import EvmYul.Wheels
import EvmYul.PerformIO
import EvmYul.Python
import Conform.Wheels

def blobBN_MUL (x₀ y₀ n : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ n
  where pythonCommandOfInput (x₀ y₀ n : String) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["bn-mul", x₀, y₀, n]
  }

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  match blobBN_MUL (toHex x₀) (toHex y₀) (toHex n) with
    | "error" => .error "BN_MUL failed"
    | s => ByteArray.ofBlob s

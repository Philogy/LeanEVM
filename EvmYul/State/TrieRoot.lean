import EvmYul.PerformIO
import EvmYul.Python
import EvmYul.Wheels

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  -- dbg_trace s!"called blobComputeTrieRoot with an array of size {ws.size}"
  -- dbg_trace s!"called blobComputeTrieRoot with data {ws[0]!.2.length}"
  
  totallySafePerformIO do
    /-
      This 'using a file trick' to get around big command line arguments should probably go
      at some point.
    -/
    let payload := ws.foldl (init := "") λ acc s ↦ acc ++ s.1 ++ "\n" ++ s.2 ++ "\n"
    let entropy ← IO.getRandomBytes 3
    let entropy' ← IO.monoNanosNow
    let inputFile := (← IO.FS.createTempDir) / s!"trieInput_{entropy}{entropy'}.txt"
    IO.FS.writeFile inputFile payload
    let result ← IO.Process.run (pythonCommandOfInput inputFile.toString ws)
    IO.FS.removeFile inputFile
    pure result
 where
  pythonCommandOfInput (inputFile : String) (ws : Array (String × String)) : IO.Process.SpawnArgs := {
    cmd := evmrsExe,
    args := #["trie-root", inputFile, ws.size.repr]
  }

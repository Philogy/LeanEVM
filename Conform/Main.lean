import Conform.TestRunner
import Evm.FFI.ffi

def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open Evm.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open Evm.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (elapsedMs : ℕ) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result} -- {elapsedMs}ms\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

/--
Parse a fixture file once and spawn one pool task per (filtered) test —
the parsed JSON is shared by reference across the file's test tasks. Returns
the spawned tasks; the caller awaits them, so workers never block on nested
waits.
-/
def spawnFileTests (path : System.FilePath) (isToBeTested : String → Bool)
    (runOne : System.FilePath → Lean.Json → String ->
      IO (Array Evm.Conform.TestId × Array (Evm.Conform.TestId × Evm.Conform.TestResult × Nat))) :
    IO (Array (Task (Except IO.Error (Array Evm.Conform.TestId × Array (Evm.Conform.TestId × Evm.Conform.TestResult × Nat))))) := do
  let file ← Lean.Json.fromFile path
  let names := (Evm.Conform.Parser.testNamesOfTest file).toOption.getD #[] |>.filter isToBeTested
  let mut subtasks := #[]
  for name in names do
    subtasks := subtasks.push (←IO.asTask (runOne path file name))
  return subtasks

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (fileFilter         : String := "")
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false)
              (expectedToFail     : Std.HashSet String := {})
              (failFast           : Bool := false) : IO (Nat × Array String) := do
  let isToBeTested (testname : String) : Bool :=
    let whitelist := testWhitelist
    let blacklist := testBlacklist ++ Evm.Conform.GlobalBlacklist
    testname ∉ blacklist ∧ (whitelist.isEmpty ∨ testname ∈ whitelist)

  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir root (pure <| · ∉ directoryBlacklist)

  let testFiles := testFiles.filter (· ∉ fileBlacklist)
  let testFiles := testFiles.filter
    λ f ↦ fileFilter.isEmpty || (f.toString.splitOn fileFilter).length != 1

  let mut discardedFiles : Array Evm.Conform.TestId := #[]
  let mut numSuccess := 0

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  -- Two-level pooling: a task per file parses the JSON and spawns one task
  -- per test (sharing the parsed object); the main thread flattens and awaits
  -- the per-test tasks. No task ever blocks on another, so the worker pool
  -- stays saturated until the global test queue itself drains.
  let progress ← IO.mkRef ((0, 0, 0) : Nat × Nat × Nat)
  let abort ← IO.mkRef false
  let runOne (path : System.FilePath) (file : Lean.Json) (name : String) :
      IO (Array Evm.Conform.TestId × Array (Evm.Conform.TestId × Evm.Conform.TestResult × Nat)) := do
    if failFast ∧ (← abort.get) then
      return (#[], #[])
    let r ← Evm.Conform.processSingleTest path file name
    for ((f, t), res, ms) in r.2 do
      log f t res ms phase
      if res.isSome then
        let id := s!"{f.fileName.getD f.toString}[{t}]"
        if expectedToFail.contains id then
          IO.println s!"XFAIL (expected) {id}"
        else
          IO.println s!"FAIL {id}"
          if failFast then
            IO.println "fail-fast: aborting remaining tests"
            abort.set true
    let (ts, fl, xf) ← progress.modifyGet λ (ts, fl, xf) ↦
      let fails := r.2.filter (·.2.1.isSome) |>.size
      let isXf := r.2.any λ ((f, t), res, _) ↦
        res.isSome ∧ expectedToFail.contains s!"{f.fileName.getD f.toString}[{t}]"
      let v := (ts + r.2.size, fl + (if isXf then 0 else fails), xf + (if isXf then fails else 0))
      (v, v)
    if ts % 500 == 0 ∧ ts != 0 then
      IO.println s!"[{ts} tests done, {fl} failed, {xf} xfail]"
      (← IO.getStdout).flush
    pure r

  IO.println s!"Scheduling {testFiles.size} test files for parallel execution..."
  let mut spawners : Array (Task _) := .empty
  for path in testFiles do
    spawners := spawners.push (←IO.asTask (spawnFileTests path isToBeTested runOne))

  let mut failedTests : Array String := .empty

  IO.println s!"Running..."
  let mut testTasks : Array (Task _) := .empty
  for s in spawners do
    testTasks := testTasks.append (←IO.ofExcept (←IO.wait s))
  IO.println s!"All {testTasks.size} test tasks spawned."
  let testResults ← testTasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res, _) in batch do
      if res.isNone
      then numSuccess := numSuccess + 1
      else failedTests := failedTests.push s!"{file.fileName.getD file.toString}[{test}]"
  return (numSuccess, failedTests)

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trim.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do
  -- `--fail-fast`: the first failure outside ExpectedToFail aborts the run.
  -- `--perf`: also run the throughput tests (vmPerformance + blake2f max
  -- rounds) — minutes each, they stress raw interpreter speed, not semantics.
  let failFastFlag := args.contains "--fail-fast"
  let perfFlag := args.contains "--perf"
  let args := args.filter (λ a ↦ a ≠ "--fail-fast" ∧ a ≠ "--perf")
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let ExpectedToFail : Std.HashSet String := {
    "invalid_block_blob_count.json[src/GeneralStateTestsFiller/Pyspecs/cancun/eip4844_blobs/test_blob_txs.py::test_invalid_block_blob_count[fork_Cancun-blockchain_test--blobs_per_tx_(7,)]]",
    "GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast.json[GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast_Cancun]"
  }

  -- Throughput stress tests (minutes each): excluded from the default
  -- conformance run, included with `--perf` (alongside vmPerformance/).
  let PerfTests : Array String := #["CALLBlake2f_MaxRounds_d0g0v0_Cancun"]

  let printResults (result : ℕ × Array String) : IO (Array String) := do
    let (success, failure) := result
    let (xfail, unexpected) := failure.partition ExpectedToFail.contains
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"Succeeded: {success}"
    IO.println s!"Failed (unexpected): {unexpected.size}"
    IO.println s!"Expected-to-fail (passing as expected): {xfail.size}"
    if !unexpected.isEmpty then IO.println s!"Failed tests:\n{unexpected}"
    return failure

  -- Optional second CLI arg: substring filter on fixture file paths.
  -- Runs only matching files in a single phase — for quick samples and profiling.
  if let some pat := args[1]? then
    let failed ← testFiles (root := "EthereumTests/BlockchainTests/")
                           (fileFilter := pat)
                           (phase := 0)
                           (threads := NumThreads)
                           (expectedToFail := ExpectedToFail)
                           (failFast := failFastFlag) >>= printResults
    return if (Std.HashSet.ofArray failed |>.diff ExpectedToFail).isEmpty then 0 else 1

  IO.println s!"Phase 1 - Conformance."
  let failed₁ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
                          (testBlacklist := PerfTests)
                          (phase := 1)
                          (threads := NumThreads)
                          (expectedToFail := ExpectedToFail)
                          (failFast := failFastFlag) >>= printResults

  if !perfFlag then
    return if (Std.HashSet.ofArray failed₁ |>.diff ExpectedToFail).isEmpty then 0 else 1

  IO.println s!"Phase 2 - Throughput tests (--perf)."
  let failed₂ ← testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
                          (phase := 2)
                          (threads := NumThreads)
                          (expectedToFail := ExpectedToFail)
                          (failFast := failFastFlag) >>= printResults

  let failed₃ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testWhitelist := PerfTests)
                          (phase := 3)
                          (threads := NumThreads)
                          (expectedToFail := ExpectedToFail)
                          (failFast := failFastFlag) >>= printResults

  return if (Std.HashSet.ofArray (failed₁ ++ failed₂ ++ failed₃) |>.diff ExpectedToFail).isEmpty then 0 else 1

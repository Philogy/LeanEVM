import Conform.TestRunner
import Evm.FFI.ffi

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

private def basicSuccess (name : System.FilePath)
                         (result : Batteries.RBMap String Evm.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Batteries.RBMap String Evm.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keys, failed.keys)

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open Evm.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open Evm.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (fileFilter         : String := "")
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false)
              (failFast           : Option (Std.HashSet String) := .none) : IO (Nat × Array String) := do
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

  -- One task per fixture file; each file is parsed exactly once, inside its
  -- task. The runtime's task pool load-balances the files across workers
  -- (pool size = LEAN_NUM_THREADS, defaulting to the hardware core count).
  -- Each task reports completion through a shared counter, so progress
  -- (`[k/M files, n tests, f failed]`) and failures stream live.
  let progress ← IO.mkRef ((0, 0, 0) : ℕ × ℕ × ℕ)
  let abort ← IO.mkRef false
  let numFiles := testFiles.size
  let mut tasks : Array (Task _) := .empty
  IO.println s!"Scheduling {numFiles} test files for parallel execution..."
  for path in testFiles do
    tasks := tasks.push <| ←IO.asTask do
      if failFast.isSome ∧ (← abort.get) then
        pure (#[], #[])
      else
      let r ← Evm.Conform.processTestFile path isToBeTested (if timed then .some 0 else .none)
        (abort := if failFast.isSome then some abort else none)
      let batchFails := r.2.filter (·.2.isSome)
      for ((file, test), _) in batchFails do
        IO.println s!"FAIL {file.fileName.getD file.toString}[{test}]"
        if let some expected := failFast then
          if !expected.contains s!"{file.fileName.getD file.toString}[{test}]" then
            IO.println "fail-fast: aborting remaining tests"
            abort.set true
      let (fs, ts, fl) ← progress.modifyGet λ (fs, ts, fl) ↦
        let v := (fs + 1, ts + r.2.size, fl + batchFails.size)
        (v, v)
      IO.println s!"[{fs}/{numFiles} files, {ts} tests, {fl} failed]"
      pure r

  let mut failedTests : Array String := .empty

  IO.println s!"Running..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res) in batch do
      log file test res phase
      if res.isNone
      then numSuccess := numSuccess + 1
      else failedTests := failedTests.push s!"{file.fileName.getD file.toString}[{test}]"
  return (numSuccess, failedTests)

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trim.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do
  -- `--fail-fast`: the first failure outside ExpectedToFail aborts the run.
  let failFastFlag := args.contains "--fail-fast"
  let args := args.filter (· ≠ "--fail-fast")
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let ExpectedToFail : Std.HashSet String := {
    "invalid_block_blob_count.json[src/GeneralStateTestsFiller/Pyspecs/cancun/eip4844_blobs/test_blob_txs.py::test_invalid_block_blob_count[fork_Cancun-blockchain_test--blobs_per_tx_(7,)]]",
    "GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast.json[GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast_Cancun]"
  }
  let ff : Option (Std.HashSet String) := if failFastFlag then some ExpectedToFail else none

  let DelayFiles : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun",
      "SuicideIssue_Cancun"]

  let printResults (result : ℕ × Array String) : IO (Array String) := do
    let (success, failure) := result
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
    IO.println s!"Succeeded: {success}"
    IO.println s!"Success rate of: {(success.toFloat / (failure.size + success).toFloat) * 100.0}"
    IO.println s!"Failed tests:\n{failure}"
    return failure

  -- Optional second CLI arg: substring filter on fixture file paths.
  -- Runs only matching files in a single phase — for quick samples and profiling.
  if let some pat := args[1]? then
    let failed ← testFiles (root := "EthereumTests/BlockchainTests/")
                           (fileFilter := pat)
                           (phase := 0)
                           (threads := NumThreads)
                           (failFast := ff) >>= printResults
    return if (Std.HashSet.ofArray failed |>.diff ExpectedToFail).isEmpty then 0 else 1

  IO.println s!"Phase 1/3 - No performance tests."
  let failed₁ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
                          (testBlacklist := DelayFiles)
                          (phase := 1)
                          (threads := NumThreads)
                          (failFast := ff) >>= printResults
  
  IO.println s!"Phase 2/3 - Performance tests only."
  let failed₂ ← testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
                          (phase := 2)
                          (threads := NumThreads)
                          (failFast := ff) >>= printResults


  IO.println s!"Phase 3/3 - Individually scheduled tests."
  let failed₃ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testWhitelist := DelayFiles)
                          (phase := 3)
                          (threads := NumThreads)
                          (failFast := ff) >>= printResults

  return if (Std.HashSet.ofArray (failed₁ ++ failed₂ ++ failed₃) |>.diff ExpectedToFail).isEmpty then 0 else 1

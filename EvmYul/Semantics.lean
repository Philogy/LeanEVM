import EvmYul.Operations


import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.PrimOps
import EvmYul.EVM.StateOps
import EvmYul.Wheels

import EvmYul.UInt256
import EvmYul.StateOps
import EvmYul.SharedStateOps
import EvmYul.MachineStateOps

import EvmYul.SpongeHash.Keccak256

--

import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

--

namespace EvmYul

section Semantics

open Stack

/--
`Transformer` is the primop-evaluating semantic function type for `Yul` and `EVM`.

- `EVM` is `EVM.State → EVM.State` because the arguments are already contained in `EVM.State.stack`.
- `Yul` is `Yul.State × List Literal → Yul.State × Option Literal` because the evaluation of primops in Yul
  does *not* store results within the state.

Both operations happen in their respecitve `.Exception` error monad.
-/
private abbrev Transformer (_ : OperationType) : Type := EVM.Transformer

private def dispatchInvalid (τ : OperationType) : Transformer τ :=
  λ _ ↦ .error .InvalidInstruction

private def dispatchUnary (τ : OperationType) : Primop.Unary → Transformer τ :=
  EVM.execUnOp

private def dispatchBinary (τ : OperationType) : Primop.Binary → Transformer τ :=
  EVM.execBinOp

private def dispatchTernary (τ : OperationType) : Primop.Ternary → Transformer τ :=
  EVM.execTriOp

private def dispatchQuartiary (τ : OperationType) : Primop.Quaternary → Transformer τ :=
  EVM.execQuadOp

private def dispatchExecutionEnvOp (τ : OperationType) (op : ExecutionEnv .EVM → UInt256) : Transformer τ :=
  EVM.executionEnvOp op

private def dispatchUnaryExecutionEnvOp (τ : OperationType) (op : ExecutionEnv .EVM → UInt256 → UInt256) : Transformer τ :=
  EVM.unaryExecutionEnvOp op

private def dispatchMachineStateOp (τ : OperationType) (op : MachineState → UInt256) : Transformer τ :=
  EVM.machineStateOp op

private def dispatchUnaryStateOp (τ : OperationType) (op : State .EVM → UInt256 → State .EVM × UInt256) : Transformer τ :=
  EVM.unaryStateOp op

private def dispatchTernaryCopyOp
 (τ : OperationType) (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM) :
  Transformer τ
:=
  EVM.ternaryCopyOp op

private def dispatchQuaternaryCopyOp
 (τ : OperationType) (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM) :
  Transformer τ
:=
  EVM.quaternaryCopyOp op

private def dispatchBinaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  EVM.binaryMachineStateOp op

private def dispatchTernaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  EVM.ternaryMachineStateOp op

private def dispatchBinaryMachineStateOp'
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer τ
:=
  EVM.binaryMachineStateOp' op

private def dispatchBinaryStateOp
 (τ : OperationType) (op : State .EVM → UInt256 → UInt256 → State .EVM) :
  Transformer τ
:=
  EVM.binaryStateOp op

private def dispatchStateOp (τ : OperationType) (op : State .EVM → UInt256) : Transformer τ :=
  EVM.stateOp op

private def dispatchLog0 (τ : OperationType) : Transformer τ :=
  EVM.log0Op

private def dispatchLog1 (τ : OperationType) : Transformer τ :=
  EVM.log1Op

private def dispatchLog2 (τ : OperationType) : Transformer τ :=
  EVM.log2Op

private def dispatchLog3 (τ : OperationType) : Transformer τ :=
  EVM.log3Op

private def dispatchLog4 (τ : OperationType) : Transformer τ :=
  EVM.log4Op

private def L (n : ℕ) := n - n / 64

def dup (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

def step (op : Operation .EVM) (arg : Option (UInt256 × Nat) := .none) : EVM.Transformer :=
  match op with
    -- TODO: Revisit STOP, this is likely not the best way to do it.
    | .STOP =>
      λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
    | .ADD =>
      dispatchBinary .EVM UInt256.add
    | .MUL =>
      dispatchBinary .EVM UInt256.mul
    | .SUB =>
      dispatchBinary .EVM UInt256.sub
    | .DIV =>
      dispatchBinary .EVM UInt256.div
    | .SDIV =>
      dispatchBinary .EVM UInt256.sdiv
    | .MOD =>
      dispatchBinary .EVM UInt256.mod
    | .SMOD =>
      dispatchBinary .EVM UInt256.smod
    | .ADDMOD =>
      dispatchTernary .EVM UInt256.addMod
    | .MULMOD =>
      dispatchTernary .EVM UInt256.mulMod
    | .EXP =>
      dispatchBinary .EVM UInt256.exp
    | .SIGNEXTEND =>
      dispatchBinary .EVM UInt256.signextend
    | .LT =>
      dispatchBinary .EVM UInt256.lt
    | .GT =>
      dispatchBinary .EVM UInt256.gt
    | .SLT =>
      dispatchBinary .EVM UInt256.slt
    | .SGT =>
      dispatchBinary .EVM UInt256.sgt
    | .EQ =>
      dispatchBinary .EVM UInt256.eq
    | .ISZERO =>
      dispatchUnary .EVM UInt256.isZero
    | .AND =>
      dispatchBinary .EVM UInt256.land
    | .OR =>
      dispatchBinary .EVM UInt256.lor
    | .XOR =>
      dispatchBinary .EVM UInt256.xor
    | .NOT =>
      dispatchUnary .EVM UInt256.lnot
    | .BYTE =>
      dispatchBinary .EVM UInt256.byteAt
    | .SHL =>
      dispatchBinary .EVM (flip UInt256.shiftLeft)
    | .SHR =>
      dispatchBinary .EVM (flip UInt256.shiftRight)
    | .SAR =>
      dispatchBinary .EVM UInt256.sar

    | .KECCAK256 =>
      dispatchBinaryMachineStateOp' .EVM MachineState.keccak256

    | .ADDRESS =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | .BALANCE =>
      dispatchUnaryStateOp .EVM EvmYul.State.balance
    | .ORIGIN =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | .CALLER =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | .CALLVALUE =>
      dispatchExecutionEnvOp .EVM ExecutionEnv.weiValue
    | .CALLDATALOAD =>
      dispatchUnaryStateOp .EVM (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | .CALLDATASIZE =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
    | .CALLDATACOPY =>
      dispatchTernaryCopyOp .EVM .calldatacopy
    | .CODESIZE =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | .CODECOPY =>
      dispatchTernaryCopyOp .EVM .codeCopy
    | .GASPRICE =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ ExecutionEnv.gasPrice)
    | .EXTCODESIZE =>
      dispatchUnaryStateOp .EVM EvmYul.State.extCodeSize
    | .EXTCODECOPY =>
      dispatchQuaternaryCopyOp .EVM EvmYul.SharedState.extCodeCopy'
    | .RETURNDATASIZE =>
      dispatchMachineStateOp .EVM EvmYul.MachineState.returndatasize
    | .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .EXTCODEHASH => dispatchUnaryStateOp .EVM EvmYul.State.extCodeHash

    | .BLOCKHASH => dispatchUnaryStateOp .EVM (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | .COINBASE => dispatchStateOp .EVM (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | .TIMESTAMP =>
      dispatchStateOp .EVM EvmYul.State.timeStamp
    | .NUMBER => dispatchStateOp .EVM EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | .PREVRANDAO => dispatchExecutionEnvOp .EVM EvmYul.prevRandao
    | .GASLIMIT => dispatchStateOp .EVM EvmYul.State.gasLimit
    | .CHAINID => dispatchStateOp .EVM EvmYul.State.chainId
    | .SELFBALANCE => dispatchStateOp .EVM EvmYul.State.selfbalance
    | .BASEFEE => dispatchExecutionEnvOp .EVM EvmYul.basefee
    | .BLOBHASH => dispatchUnaryExecutionEnvOp .EVM blobhash
    | .BLOBBASEFEE => dispatchExecutionEnvOp .EVM EvmYul.ExecutionEnv.getBlobGasprice

    | .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow
    | .MSTORE =>
      dispatchBinaryMachineStateOp .EVM MachineState.mstore
    | .MSTORE8 => dispatchBinaryMachineStateOp .EVM MachineState.mstore8
    | .SLOAD =>
      dispatchUnaryStateOp .EVM EvmYul.State.sload
    | .SSTORE =>
      dispatchBinaryStateOp .EVM EvmYul.State.sstore
    | .TLOAD => dispatchUnaryStateOp .EVM EvmYul.State.tload
    | .TSTORE => dispatchBinaryStateOp .EVM EvmYul.State.tstore
    | .MSIZE => dispatchMachineStateOp .EVM MachineState.msize
    | .GAS =>
      dispatchMachineStateOp .EVM MachineState.gas
    | .MCOPY => dispatchTernaryMachineStateOp .EVM MachineState.mcopy

    | .LOG0 => dispatchLog0 .EVM
    | .LOG1 => dispatchLog1 .EVM
    | .LOG2 => dispatchLog2 .EVM
    | .LOG3 => dispatchLog3 .EVM
    | .LOG4 => dispatchLog4 .EVM
    | .RETURN => dispatchBinaryMachineStateOp .EVM MachineState.evmReturn
    | .REVERT => dispatchBinaryMachineStateOp .EVM MachineState.evmRevert
    | .SELFDESTRUCT =>
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let Iₐ := evmState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 μ₁
            if evmState.createdAccounts.contains Iₐ then
              -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
              let A' : Substate :=
                { evmState.substate with
                    selfDestructSet :=
                      evmState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == 0 then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account .EVM) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := 0}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := 0}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          evmState.accountMap.insert r {σ_r with balance := 0}
                            |>.insert Iₐ {σ_Iₐ with balance := 0}
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
            else
              /- When SELFDESTRUCT is executed in a transaction that is not the
                same as the contract calling SELFDESTRUCT was created:
              -/
              let A' : Substate :=
                { evmState.substate with
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == 0 then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account .EVM) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := 0}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := 0}
                        else
                          -- Note that if the target is the same as the contract
                          -- calling SELFDESTRUCT there is no net change in balances.
                          -- Unlike the prior specification, Ether will not be burnt in this case.
                          evmState.accountMap
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow
    | .INVALID => dispatchInvalid .EVM
    | .Push .PUSH0 => λ evmState =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push 0)
    | .Push _ => λ evmState => do
        let some (arg, argWidth) := arg | .error .StackUnderflow
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
    | .JUMP => λ evmState => do
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .JUMPI => λ evmState => do
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ != 0 then μ₀ else evmState.pc + 1
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .PC => λ evmState =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
    | .JUMPDEST => λ evmState => do
        .ok <| evmState.incrPC
    | .DUP1 => dup 1
    | .DUP2 => dup 2
    | .DUP3 => dup 3
    | .DUP4 => dup 4
    | .DUP5 => dup 5
    | .DUP6 => dup 6
    | .DUP7 => dup 7
    | .DUP8 => dup 8
    | .DUP9 => dup 9
    | .DUP10 => dup 10
    | .DUP11 => dup 11
    | .DUP12 => dup 12
    | .DUP13 => dup 13
    | .DUP14 => dup 14
    | .DUP15 => dup 15
    | .DUP16 => dup 16
    | .SWAP1 => swap 1
    | .SWAP2 => swap 2
    | .SWAP3 => swap 3
    | .SWAP4 => swap 4
    | .SWAP5 => swap 5
    | .SWAP6 => swap 6
    | .SWAP7 => swap 7
    | .SWAP8 => swap 8
    | .SWAP9 => swap 9
    | .SWAP10 => swap 10
    | .SWAP11 => swap 11
    | .SWAP12 => swap 12
    | .SWAP13 => swap 13
    | .SWAP14 => swap 14
    | .SWAP15 => swap 15
    | .SWAP16 => swap 16
    | _ => λ _ ↦ default


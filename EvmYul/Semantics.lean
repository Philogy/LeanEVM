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

private def L (n : ℕ) := n - n / 64

def dup (n : ℕ) : EVM.Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : EVM.Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

def step (op : Operation) (arg : Option (UInt256 × Nat) := .none) : EVM.Transformer :=
  match op with
    -- TODO: Revisit STOP, this is likely not the best way to do it.
    | .STOP =>
      λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
    | .ADD =>
      EVM.execBinOp UInt256.add
    | .MUL =>
      EVM.execBinOp UInt256.mul
    | .SUB =>
      EVM.execBinOp UInt256.sub
    | .DIV =>
      EVM.execBinOp UInt256.div
    | .SDIV =>
      EVM.execBinOp UInt256.sdiv
    | .MOD =>
      EVM.execBinOp UInt256.mod
    | .SMOD =>
      EVM.execBinOp UInt256.smod
    | .ADDMOD =>
      EVM.execTriOp UInt256.addMod
    | .MULMOD =>
      EVM.execTriOp UInt256.mulMod
    | .EXP =>
      EVM.execBinOp UInt256.exp
    | .SIGNEXTEND =>
      EVM.execBinOp UInt256.signextend
    | .LT =>
      EVM.execBinOp UInt256.lt
    | .GT =>
      EVM.execBinOp UInt256.gt
    | .SLT =>
      EVM.execBinOp UInt256.slt
    | .SGT =>
      EVM.execBinOp UInt256.sgt
    | .EQ =>
      EVM.execBinOp UInt256.eq
    | .ISZERO =>
      EVM.execUnOp UInt256.isZero
    | .AND =>
      EVM.execBinOp UInt256.land
    | .OR =>
      EVM.execBinOp UInt256.lor
    | .XOR =>
      EVM.execBinOp UInt256.xor
    | .NOT =>
      EVM.execUnOp UInt256.lnot
    | .BYTE =>
      EVM.execBinOp UInt256.byteAt
    | .SHL =>
      EVM.execBinOp (flip UInt256.shiftLeft)
    | .SHR =>
      EVM.execBinOp (flip UInt256.shiftRight)
    | .SAR =>
      EVM.execBinOp UInt256.sar

    | .KECCAK256 =>
      EVM.binaryMachineStateOp' MachineState.keccak256

    | .ADDRESS =>
      EVM.executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | .BALANCE =>
      EVM.unaryStateOp EvmYul.State.balance
    | .ORIGIN =>
      EVM.executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | .CALLER =>
      EVM.executionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | .CALLVALUE =>
      EVM.executionEnvOp ExecutionEnv.weiValue
    | .CALLDATALOAD =>
      EVM.unaryStateOp (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | .CALLDATASIZE =>
      EVM.executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
    | .CALLDATACOPY =>
      EVM.ternaryCopyOp .calldatacopy
    | .CODESIZE =>
      EVM.executionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | .CODECOPY =>
      EVM.ternaryCopyOp .codeCopy
    | .GASPRICE =>
      EVM.executionEnvOp (.ofNat ∘ ExecutionEnv.gasPrice)
    | .EXTCODESIZE =>
      EVM.unaryStateOp EvmYul.State.extCodeSize
    | .EXTCODECOPY =>
      EVM.quaternaryCopyOp EvmYul.SharedState.extCodeCopy'
    | .RETURNDATASIZE =>
      EVM.machineStateOp EvmYul.MachineState.returndatasize
    | .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .EXTCODEHASH => EVM.unaryStateOp EvmYul.State.extCodeHash

    | .BLOCKHASH => EVM.unaryStateOp (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | .COINBASE => EVM.stateOp (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | .TIMESTAMP =>
      EVM.stateOp EvmYul.State.timeStamp
    | .NUMBER => EVM.stateOp EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | .PREVRANDAO => EVM.executionEnvOp EvmYul.prevRandao
    | .GASLIMIT => EVM.stateOp EvmYul.State.gasLimit
    | .CHAINID => EVM.stateOp EvmYul.State.chainId
    | .SELFBALANCE => EVM.stateOp EvmYul.State.selfbalance
    | .BASEFEE => EVM.executionEnvOp EvmYul.basefee
    | .BLOBHASH => EVM.unaryExecutionEnvOp blobhash
    | .BLOBBASEFEE => EVM.executionEnvOp EvmYul.ExecutionEnv.getBlobGasprice

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
      EVM.binaryMachineStateOp MachineState.mstore
    | .MSTORE8 => EVM.binaryMachineStateOp MachineState.mstore8
    | .SLOAD =>
      EVM.unaryStateOp EvmYul.State.sload
    | .SSTORE =>
      EVM.binaryStateOp EvmYul.State.sstore
    | .TLOAD => EVM.unaryStateOp EvmYul.State.tload
    | .TSTORE => EVM.binaryStateOp EvmYul.State.tstore
    | .MSIZE => EVM.machineStateOp MachineState.msize
    | .GAS =>
      EVM.machineStateOp MachineState.gas
    | .MCOPY => EVM.ternaryMachineStateOp MachineState.mcopy

    | .LOG0 => EVM.log0Op
    | .LOG1 => EVM.log1Op
    | .LOG2 => EVM.log2Op
    | .LOG3 => EVM.log3Op
    | .LOG4 => EVM.log4Op
    | .RETURN => EVM.binaryMachineStateOp MachineState.evmReturn
    | .REVERT => EVM.binaryMachineStateOp MachineState.evmRevert
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
                            {(default : Account) with balance := σ_Iₐ.balance}
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
                            {(default : Account) with balance := σ_Iₐ.balance}
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
    | .INVALID => (λ _ ↦ .error .InvalidInstruction)
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


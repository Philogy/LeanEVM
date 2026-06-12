import Evm.Machine.Stack

import Evm.State
import Evm.Exception
import Evm.StateOps
import Evm.Machine.SharedStateOps
import Evm.Machine.ExecutionState
import Evm.Machine.ExecutionStateOps

namespace Evm



def Transformer := ExecutionState → Except ExecutionException ExecutionState

def execUnOp (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.stack.pop with
      | some ⟨stack, a⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f a)
      | _ =>
        .error .StackUnderflow

def execBinOp (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.stack.pop2 with
      | some ⟨stack, a, b⟩ => Id.run do
        let result := f a b
        .ok <| s.replaceStackAndIncrPC (stack.push result)
      | _ =>
        .error .StackUnderflow

def execTriOp (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.stack.pop3 with
      | some ⟨stack, a, b, c⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f a b c)
      | _ =>
        .error .StackUnderflow

def executionEnvOp (op : ExecutionEnv → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.executionEnv
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def unaryExecutionEnvOp (op : ExecutionEnv → UInt256 → UInt256) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop with
    | some ⟨ s , a⟩ => Id.run do
      let result := op evmState.executionEnv a
      .ok <|
        evmState.replaceStackAndIncrPC (s.push result)
    | _ => .error .StackUnderflow

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.toMachineState
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , a, b ⟩ => Id.run do
      let mState' := op evmState.toMachineState a b
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , a, b ⟩ => Id.run do
      let (val, mState') := op evmState.toMachineState a b
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error .StackUnderflow

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ s , a, b, c ⟩ => Id.run do
      let mState' := op evmState.toMachineState a b c
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryStateOp
  (op : Evm.State → UInt256 → UInt256 → Evm.State)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , a, b ⟩ => Id.run do
      let state' := op evmState.toState a b
      let evmState' := {evmState with toState := state'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def stateOp (op : Evm.State → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toState)

def unaryStateOp
  (op : Evm.State → UInt256 → Evm.State × UInt256)
    :
  Transformer
:= λ evmState ↦
      match evmState.stack.pop with
        | some ⟨stack' , a ⟩ => Id.run do
          let (state', b) := op evmState.toState a
          let evmState' := {evmState with toState := state'}
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error .StackUnderflow

def ternaryCopyOp
  (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ stack' , a, b, c⟩ => Id.run do
      let sState' := op evmState.toSharedState a b c
      let evmState' := { evmState with toSharedState := sState'}
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error .StackUnderflow

def quaternaryCopyOp
  (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState)
    :
  Transformer
:=  λ evmState ↦
      match evmState.stack.pop4 with
        | some ⟨ stack' , a, b, c, d⟩ => Id.run do
          let sState' := op evmState.toSharedState a b c d
          let evmState' := { evmState with toSharedState := sState'}
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow

private def evmLogOp (evmState : ExecutionState) (a b : UInt256) (t : Array UInt256) : ExecutionState :=
  let sharedState' := SharedState.logOp a b t evmState.toSharedState
  { evmState with toSharedState := sharedState'}

def log0Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop2 with
      | some ⟨stack', a, b⟩ => Id.run do
        let evmState' := evmLogOp evmState a b #[]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log1Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop3 with
      | some ⟨stack', a, b, c⟩ => Id.run do
        let evmState' := evmLogOp evmState a b #[c]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log2Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop4 with
      | some ⟨stack', a, b, c, d⟩ => Id.run do
        let evmState' := evmLogOp evmState a b #[c, d]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log3Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop5 with
      | some ⟨stack', a, b, c, d, μ₄⟩ => Id.run do
        let evmState' := evmLogOp evmState a b #[c, d, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log4Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop6 with
      | some ⟨stack', a, b, c, d, μ₄, μ₅⟩ => Id.run do
        let evmState' := evmLogOp evmState a b #[c, d, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow



end Evm

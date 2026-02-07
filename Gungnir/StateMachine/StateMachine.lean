/-
  StateMachine.lean - Generic state machine framework for verified Kubernetes operators

  This module provides a TLA-style state machine framework inspired by the Anvil project
  (OSDI'24). It defines generic types for states, actions, steps, and transitions that
  can be instantiated for specific controllers (e.g., Valkey reconciler, Sentinel monitor).

  Key types:
  - Action: A guarded transition with a precondition and a transition function
  - ActionResult: The result of attempting an action (Enabled or Disabled)
  - StateMachine: A collection of actions indexed by steps, with an init predicate

  Reference: anvil/src/state_machine/state_machine.rs
-/

namespace Gungnir.StateMachine

-- An Action is a guarded transition: it has a precondition that must hold for the
-- transition to fire, and a transition function that produces a new state and output.
structure Action (State : Type) (Input : Type) (Output : Type) where
  /-- The condition that enables this action -/
  precondition : Input -> State -> Prop
  /-- The transition function producing (new_state, output) -/
  transition : Input -> State -> State × Output

-- The result of attempting to take an action at a given state.
inductive ActionResult (State : Type) (Output : Type) where
  | Disabled : ActionResult State Output
  | Enabled : State -> Output -> ActionResult State Output

-- A StateMachine bundles:
-- - An initial state predicate
-- - A step type that indexes available actions
-- - A mapping from steps to actions
-- - A mapping from (step, external_input) to action_input
structure StateMachine (State : Type) (Input : Type) (ActionInput : Type)
    (Output : Type) (Step : Type) where
  /-- Predicate characterizing valid initial states -/
  init : State -> Prop
  /-- Map a step to its corresponding action -/
  stepToAction : Step -> Action State ActionInput Output
  /-- Derive the action input from the step and external input -/
  actionInput : Step -> Input -> ActionInput

-- Prop-level next-state relation: there exists a step such that the action fires
-- and produces s'.
def StateMachine.next {State Input ActionInput Output Step : Type}
    (sm : StateMachine State Input ActionInput Output Step)
    (input : Input) (s s' : State) : Prop :=
  ∃ step : Step,
    (sm.stepToAction step).precondition (sm.actionInput step input) s ∧
    s' = ((sm.stepToAction step).transition (sm.actionInput step input) s).1

-- The pre (enabled) predicate for a specific action with a given input.
def Action.pre {State Input Output : Type}
    (action : Action State Input Output) (input : Input) : State -> Prop :=
  fun s => action.precondition input s

-- The forward relation: precondition holds at s, and s' is the result of transition.
def Action.forward {State Input Output : Type}
    (action : Action State Input Output) (input : Input) : State -> State -> Prop :=
  fun s s' =>
    action.precondition input s ∧
    s' = (action.transition input s).1

-- A NetworkStateMachine is a simplified state machine with a single "deliver" action
-- (used for modeling the network/API server layer).
structure NetworkStateMachine (State : Type) (MessageOps : Type) where
  /-- Predicate characterizing valid initial states -/
  init : State -> Prop
  /-- The single deliver action -/
  deliver : Action State MessageOps Unit

def NetworkStateMachine.next {State MessageOps : Type}
    (nsm : NetworkStateMachine State MessageOps)
    (msgOps : MessageOps) (s s' : State) : Prop :=
  nsm.deliver.precondition msgOps s ∧
  s' = (nsm.deliver.transition msgOps s).1

end Gungnir.StateMachine

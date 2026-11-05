module
public import RStsVariant2.Spec.Execution

@[expose] public section

/-!
# Observables: what a condition on executions reads of an execution, as a class

The conditions on executions of `RStsVariant2.Spec.Conditions` read a run only through a few
readings: the action of each step, the real time at which each configuration is entered, and, in
each configuration, each node's clock, each node's local state (whether it is known, and what it
is), each node's view, the sent envelopes, the corrupted set and the crashed set. The class
`Observable` names exactly these readings, and nothing else: an observable has no
protocol and no step relation. Each condition is written once over the class, so once for every
type of execution that provides these readings.

None of this is part of the bare framework. The bare framework is `RStsVariant2.Spec.Protocol`
(states and steps) and `RStsVariant2.Spec.Execution` (executions); this page changes neither. It
gives two instances of the class:

* `Exec Pr`, the executions of a protocol `Pr`: each reading is the run's own (`x.lbl j`,
  `x.stamp i`, `x[i].clock p`, `x[i][p]`, `x[i].view p`, `x[i].sent`, `x[i].adv`,
  `x[i].crashed`);
* `ObservedRun Node Msg Ev V`, an execution whose configurations carry, for each node, a value
  of a type `V` in place of its local state, and have no step relation; `observe f x` is the run
  `x` as observed, with `f` the map from a local state to `V`.

The local state is read through `state`, of a type `L` that the instance fixes: on `Exec Pr` it is
`Local Node Msg NodeState`, on an observed run it is `V`. A condition that reads what a node's state holds
(the blocks it holds, what it serves to a peer, the committee information it has) takes that
reading as a parameter over `L`.

`HonestG` and `InForceG` are the two readings of `RStsVariant2.Spec.Execution`, `Execution.Honest`
and `Execution.InForce`, written over the class. The suffix `G` marks a definition written over any
type with an `Observable`; the definitions of `RStsVariant2.Spec.Execution` keep their names.
-/

set_option autoImplicit false

namespace RStsVariant2

/-- The questions a condition may ask about a history: what happened at each step, when it
    happened, and what each node had seen. Runs and observed runs are observable.

    `Observable X Node Msg L Ev`: the executions `x : X` are observables. Not part
    of the bare framework: no step of the framework reads it.

    An observable has no protocol and no step relation. It has only what the conditions on
    executions read: the action of each step, and, for each configuration, the real time at which it
    is entered, each node's clock, each node's state if known, each node's view, the envelopes sent,
    the corrupted set and the crashed set. The class asks nothing of these: no step relation ties a
    configuration to the next, and the real times are not required to be monotone. The runs of a
    protocol `Pr` (`Exec Pr`) and the observed runs (`ObservedRun Node Msg Ev V`) are
    instances, so a condition on executions written over the class is written once for both.

    `Node`, `Msg` and `Ev` are the types of the nodes, the messages and the protocol events; `L` is
    the type of what the execution records of a node's state (on the runs of a protocol, its local
    state `Local Node Msg NodeState`; on an observed run, its value `V`). All four are fixed by
    `X`.

    Read aloud: an execution of type `X` has, for every step, its action; for every configuration,
    the real time it is entered, and in it each node's clock, each node's state if known, each
    node's view, the envelopes sent, the corrupted set and the crashed set; and nothing else. -/
class Observable (X : Type) (Node Msg L Ev : outParam Type) where
  /-- The action of step `j`. -/
  lbl : X → Nat → Action Node Msg Ev
  /-- The real time at which configuration `i` is entered; step `i` is taken at `stamp x (i + 1)`. -/
  stamp : X → Nat → ℝ
  /-- Node `p`'s clock reading in configuration `i`: `some t` while its clock exists, `none`
      otherwise. -/
  clock : X → Nat → Node → Option Time
  /-- Node `p`'s state in configuration `i`: `some l` when it is known, `none` when it is unknown
      (before the node first comes online, and from its corruption on). -/
  state : X → Nat → Node → Option L
  /-- Node `p`'s view in configuration `i`: the signed messages delivered to it so far. -/
  view : X → Nat → Node → View Node Msg
  /-- The envelopes sent up to configuration `i`, with multiplicity. -/
  sent : X → Nat → Multiset (Envelope Node Msg)
  /-- The corrupted set of configuration `i`. -/
  adv : X → Nat → Finset Node
  /-- The crashed set of configuration `i`. -/
  crashed : X → Nat → Finset Node

open Observable

/-- The executions of a protocol `Pr` are read by their own readings: the action and the stamps
    of the execution, and the fields of its configurations, a node's state being its local state
    `x[i][p]`. A reading of executions, not part of the bare framework. -/
instance {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} :
    Observable (Exec Pr) Node Msg (Local Node Msg NodeState) Ev where
  lbl x j := x.lbl j
  stamp x i := x.stamp i
  clock x i p := x[i].clock p
  state x i p := x[i][p]
  view x i p := x[i].view p
  sent x i := x[i].sent
  adv x i := x[i].adv
  crashed x i := x[i].crashed

/-- A configuration of an observed run: the fields of a configuration of `RStsVariant2.Spec.Protocol`, with
    a node's value `V` in place of its local state. Not part of the bare framework: no step relation
    reads it.

    Read aloud: each node's value, if known, each node's clock reading, if its clock exists, each
    node's view, the envelopes sent, the corrupted set and the crashed set. -/
structure TraceConfig (Node Msg V : Type) where
  /-- Each node's value: `some v` when known, `none` when unknown. -/
  nodes : Node → Option V
  /-- Each node's clock reading: `some t` while its clock exists, `none` otherwise. -/
  clock : Node → Option Time
  /-- Each node's view: the signed messages delivered to it so far. -/
  view : Node → View Node Msg
  /-- The envelopes sent so far, with multiplicity. -/
  sent : Multiset (Envelope Node Msg)
  /-- The corrupted set. -/
  adv : Finset Node
  /-- The crashed set. -/
  crashed : Finset Node

/-- One history that answers those questions: a run with each node's private state hidden, only
    what is read of it kept. It is `Observable`.

    An observed run is a sequence of configurations (`TraceConfig`), the action of each step, and the
    real time each configuration is entered, with the three conditions on the real time that an
    `Execution` has (it never goes back, it never stops, it starts at `0`). There is no step
    relation: nothing ties a configuration to the next. A node's private state is its local state;
    what is read of it is a value of the type `V`. Not part of the bare framework.

    Read aloud: configurations, actions and real times, with the real time monotone, unbounded and
    starting at `0`. -/
structure ObservedRun (Node Msg Ev V : Type) where
  /-- Configuration `i`. -/
  cfg : Nat → TraceConfig Node Msg V
  /-- The action of step `j`. -/
  lbl : Nat → Action Node Msg Ev
  /-- The real time at which configuration `i` is entered. -/
  stamp : Nat → ℝ
  /-- Real time never goes back. -/
  mono : ∀ i, stamp i ≤ stamp (i + 1)
  /-- Real time never stops. -/
  progress : ∀ r : ℝ, ∃ i, r ≤ stamp i
  /-- The observed run starts at real time `0`. -/
  init_stamp : stamp 0 = 0

/-- An observed run is read by its own fields, a node's state being its value `V`. A reading of
    executions, not part of the bare framework. -/
instance {Node Msg Ev V : Type} : Observable (ObservedRun Node Msg Ev V) Node Msg V Ev where
  lbl y j := y.lbl j
  stamp y i := y.stamp i
  clock y i p := (y.cfg i).clock p
  state y i p := (y.cfg i).nodes p
  view y i p := (y.cfg i).view p
  sent y i := (y.cfg i).sent
  adv y i := (y.cfg i).adv
  crashed y i := (y.cfg i).crashed

/-- The run `x` as observed. `f` is the map from a local state to a node's value `V`; the result has
    the same actions, stamps, clocks, views, sent envelopes, corrupted and crashed sets, and each known local
    state `l` replaced by `f l`. Not part of the bare framework.

    Read aloud: the run with each node's local state replaced by its image under `f`. -/
def observe {Node Msg NodeState Ev V : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (f : Local Node Msg NodeState → V) (x : Exec Pr) :
    ObservedRun Node Msg Ev V where
  cfg i := { nodes := fun p => (x[i][p]).map f, clock := x[i].clock, view := x[i].view,
             sent := x[i].sent, adv := x[i].adv, crashed := x[i].crashed }
  lbl := x.lbl
  stamp := x.stamp
  mono := x.mono
  progress := x.progress
  init_stamp := x.init_stamp

/-- `Execution.Honest` over any `Observable`: `p` is outside the corrupted set of configuration
    `i`. A reading of executions, not part of the bare framework.

    Read aloud: `p` is not corrupted in configuration `i`. -/
def HonestG {X Node Msg L Ev : Type} [Observable X Node Msg L Ev] (x : X) (i : Nat) (p : Node) :
    Prop :=
  p ∉ adv x i

/-- `Execution.InForce` over any `Observable`: configuration `i` is in force at the real time `s`,
    entered before `s` and left at `s` or later. A reading of executions, not part of the bare
    framework.

    Read aloud: as the real time reaches `s`, configuration `i` is the one the execution is in. -/
def InForceG {X Node Msg L Ev : Type} [Observable X Node Msg L Ev] (x : X) (i : Nat) (s : ℝ) :
    Prop :=
  stamp x i < s ∧ s ≤ stamp x (i + 1)

end RStsVariant2

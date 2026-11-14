module
public import RealStsMulticastMultisetLog.Spec.Execution

@[expose] public section

/-!
# Observed runs: what a condition on executions reads of an execution

The conditions on executions of `RealStsMulticastMultisetLog.Spec.Conditions` read a run only
through a few readings: the action of each step, the real time at which each configuration is
entered, and, in each configuration, each node's clock, each node's local state (whether it is
known, and what it is), each node's view, the sent envelopes, the corrupted set and the crashed set.
An observed run (`ObservedRun Node Msg Ev V`) is exactly these readings, with a value of a type `V`
in place of each node's local state, and no step relation. Each condition is written once, on
observed runs; a condition on a run `x : Exec Pr` is the condition on its observation
`observe f x`, where `f` reads a local state as a value of `V` (`id` when the condition reads the
local state itself).

None of this is part of the bare framework. The bare framework is
`RealStsMulticastMultisetLog.Spec.Protocol` (states and steps) and
`RealStsMulticastMultisetLog.Spec.Execution` (executions); this page changes neither.

The readings of an observed run `y` are its fields `y.lbl` and `y.stamp`, and `y.clock`,
`y.state`, `y.view`, `y.sent`, `y.adv`, `y.crashed`, which read the fields of its configurations.
`HonestG` and `InForceG` are the two readings of `RealStsMulticastMultisetLog.Spec.Execution`,
`Execution.Honest` and `Execution.InForce`, written on observed runs. The suffix `G` marks a
definition written on observed runs whose run form keeps the name without it.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-- A configuration of an observed run: the fields of a configuration of
    `RealStsMulticastMultisetLog.Spec.Protocol`, with a node's value `V` in place of its local
    state. Not part of the bare framework: no step relation reads it.

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

/-- What the conditions on executions read of a history: a run with each node's private state
    hidden, only what is read of it kept.

    An observed run is a sequence of configurations (`TraceConfig`), the action of each step, and
    the real time each configuration is entered, with the three conditions on the real time that an
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
  /-- The real time at which configuration `i` is entered; step `i` is taken at `stamp (i + 1)`. -/
  stamp : Nat → ℝ
  /-- Real time never goes back. -/
  mono : ∀ i, stamp i ≤ stamp (i + 1)
  /-- Real time never stops. -/
  progress : ∀ r : ℝ, ∃ i, r ≤ stamp i
  /-- The observed run starts at real time `0`. -/
  init_stamp : stamp 0 = 0

namespace ObservedRun

variable {Node Msg Ev V : Type}

/-- Node `p`'s clock reading in configuration `i`: `some t` while its clock exists, `none`
    otherwise. -/
def clock (y : ObservedRun Node Msg Ev V) (i : Nat) (p : Node) : Option Time := (y.cfg i).clock p

/-- Node `p`'s value in configuration `i`: `some v` when it is known, `none` when it is unknown
    (before the node first comes online, and from its corruption on). -/
def state (y : ObservedRun Node Msg Ev V) (i : Nat) (p : Node) : Option V := (y.cfg i).nodes p

/-- Node `p`'s view in configuration `i`: the signed messages delivered to it so far. -/
def view (y : ObservedRun Node Msg Ev V) (i : Nat) (p : Node) : View Node Msg := (y.cfg i).view p

/-- The envelopes sent up to configuration `i`, with multiplicity. -/
def sent (y : ObservedRun Node Msg Ev V) (i : Nat) : Multiset (Envelope Node Msg) := (y.cfg i).sent

/-- The corrupted set of configuration `i`. -/
def adv (y : ObservedRun Node Msg Ev V) (i : Nat) : Finset Node := (y.cfg i).adv

/-- The crashed set of configuration `i`. -/
def crashed (y : ObservedRun Node Msg Ev V) (i : Nat) : Finset Node := (y.cfg i).crashed

end ObservedRun

/-- The run `x` as observed. `f` is the map from a local state to a node's value `V`; the result has
    the same actions, stamps, clocks, views, sent envelopes, corrupted and crashed sets, and each
    known local state `l` replaced by `f l`. Not part of the bare framework.

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

open ObservedRun

/-- `Execution.Honest` on an observed run: `p` is outside the corrupted set of configuration `i`.
    A reading of executions, not part of the bare framework.

    Read aloud: `p` is not corrupted in configuration `i`. -/
def HonestG {Node Msg Ev V : Type} (y : ObservedRun Node Msg Ev V) (i : Nat) (p : Node) : Prop :=
  p ∉ adv y i

/-- `Execution.InForce` on an observed run: configuration `i` is in force at the real time `s`,
    entered before `s` and left at `s` or later. A reading of executions, not part of the bare
    framework.

    Read aloud: as the real time reaches `s`, configuration `i` is the one the execution is in. -/
def InForceG {Node Msg Ev V : Type} (y : ObservedRun Node Msg Ev V) (i : Nat) (s : ℝ) : Prop :=
  stamp y i < s ∧ s ≤ stamp y (i + 1)

end Framework.RealStsMulticastMultisetLog

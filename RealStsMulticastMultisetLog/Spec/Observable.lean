module
public import RealStsMulticastMultisetLog.Spec.Execution

@[expose] public section

/-!
# Observed runs: what a condition on executions reads of an execution

The conditions on executions of `RealStsMulticastMultisetLog.Spec.Conditions` read a run only
through a few readings: the action of each step, the real time at which each configuration is
entered, and, in each configuration, each node's clock, each node's value (whether it is known,
and what it is), each node's view, the sent envelopes, the corrupted set and the crashed set.
An observed run (`ObservedRun`, `RealStsMulticastMultisetLog.Spec.Execution`) of observed
configurations (`ObservedConfig Node Msg V`) is exactly these readings, with a value of a type `V`
for each node. Every run is one: `Execution` extends `ObservedRun`, and a run's configuration
(`Config`) is an observed configuration whose values are local states. So a condition written on
observed runs applies to a run `π` as it is (`π.toObservedRun`), and to what is read of it,
`observe readLocal π`, where `readLocal` reads a local state as a value of `V`.

The readings of an observed run `y` are its fields `y.lbl` and `y.stamp`, and `y.clock`,
`y.state`, `y.view`, `y.sent`, `y.adv`, `y.crashed`, which read the fields of its configurations;
`y.Honest` and `y.InForce` are on the page `RealStsMulticastMultisetLog.Spec.Execution`.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

namespace ObservedRun

variable {Node Msg V Lbl : Type}

/-- Node `p`'s clock reading in configuration `i`: `some t` while its clock exists, `none`
    otherwise. -/
def clock (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) (p : Node) : Option Time :=
  (y.cfg i).clock p

/-- Node `p`'s value in configuration `i`: `some v` when it is known, `none` when it is unknown
    (before the node first comes online, and from its corruption on). -/
def state (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) (p : Node) : Option V :=
  (y.cfg i).nodes p

/-- Node `p`'s view in configuration `i`: the signed messages delivered to it so far. -/
def view (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) (p : Node) : View Node Msg :=
  (y.cfg i).view p

/-- The envelopes sent up to configuration `i`, with multiplicity. -/
def sent (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) : Multiset (Envelope Node Msg) :=
  (y.cfg i).sent

/-- The corrupted set of configuration `i`. -/
def adv (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) : Finset Node :=
  (y.cfg i).adv

/-- The crashed set of configuration `i`. -/
def crashed (y : ObservedRun (ObservedConfig Node Msg V) Lbl) (i : Nat) : Finset Node :=
  (y.cfg i).crashed

/-- The observed run `y` with each known value `w` replaced by `readValue w`; the actions, stamps,
    clocks, views, sent envelopes, corrupted and crashed sets are `y`'s.

    Read aloud: `y` with each node's value replaced by what `readValue` reads of it. -/
def map {W : Type} (readValue : (w : V) → W) (y : ObservedRun (ObservedConfig Node Msg V) Lbl) :
    ObservedRun (ObservedConfig Node Msg W) Lbl where
  cfg i := { nodes := fun p => ((y.cfg i).nodes p).map readValue, clock := (y.cfg i).clock,
             view := (y.cfg i).view, sent := (y.cfg i).sent, adv := (y.cfg i).adv,
             crashed := (y.cfg i).crashed }
  lbl := y.lbl
  stamp := y.stamp
  mono := y.mono
  progress := y.progress
  init_stamp := y.init_stamp

end ObservedRun

/-- The run `π` as observed: `readLocal` reads a node's local state as a value of `V`; the result is
    `π`'s observed run with each known local state `l` replaced by `readLocal l`. Not part of the
    bare framework.

    Read aloud: the run `π` with each node's local state replaced by what `readLocal` reads of it. -/
def observe {Node Msg NodeState Ev V : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (readLocal : (l : Local Node Msg NodeState) → V)
    (π : Exec Pr) : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev) :=
  π.toObservedRun.map readLocal

end Framework.RealStsMulticastMultisetLog

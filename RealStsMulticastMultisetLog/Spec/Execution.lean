module
public import Mathlib.Data.Real.Basic
public import RealStsMulticastMultisetLog.Spec.Protocol

@[expose] public section

/-!
# Executions in real time

Liveness is a property of executions, not of reachable states, so a state-based
`Invariant` over a `System` cannot express it. Hence `Execution`, and hence why
every network and participation assumption in this framework is a **predicate on
executions** rather than a condition on `Step`: the two models we care about impose
different ones over the same step relation.

This page holds the framework's executions and the readings of an execution: `Execution`, its
indexing, `Execution.InForce`, `Exec`, `Execution.Honest` and `Execution.Enabled`. The conditions on
executions, which statements take as hypotheses, are on the page `RealStsMulticastMultisetLog.Spec.Conditions`; the
framework assumes none of them.

**Real time is the execution's.** An execution is a sequence of configurations and steps, each
configuration entered at a real time, `Execution.stamp` (D-DNS1 (a)). The configurations carry no
time and the step relation reads none (`RealStsMulticastMultisetLog.Spec.Protocol`): the real time enters only
through the stamps, which the conditions on executions (`RealStsMulticastMultisetLog.Spec.Conditions`) read.
Several steps may share one stamp; their order
in the sequence is then any order, so a delivery and a tick taken at one real time come in either
order (D-ORD1 (b)). Two steps of one node may also share one real time. The environment's steps (a
clock change, a corruption, a crash, a restart) are steps like the others, so each happens at
whatever real time its stamp says.

The nodes' clocks are digital: `c.clock p` is an integer reading, `some t`, once `p`'s clock
exists, and `none` otherwise (no clock exists at the start, and a corruption empties it; a
validator's clock starts before it first comes online, since a restart needs it). The step that sets a reading,
`setClock p t`, happens at a real time of its own, its stamp, and runs no protocol code; every other
step of `p` reads the clock. How a reading relates to the real time at which it is set is a
condition on executions (`ClockWithinSkewR`), so that a property carries only the clock discipline
it needs.

Since 29 Oct 2026 a validator's local state may be unknown (before it first comes online, and
from its corruption on), no clock exists at the start, and a restart needs the clock
(`RealStsMulticastMultisetLog.Spec.Protocol`, section "Unknown local state"). So `ClockAdvancesWithinR`, a
condition on executions, asks every node's clock, once started at any reading, to come to every
greater reading while the node is up (not crashed, with its local state known) and not
corrupted, and asks nothing of the clock of a node crashed or not yet online; it does not ask a
clock to start. A corruption empties the validator's clock as well
as its local state, and no `setClock` is taken at a corrupted validator (D-RSV2-2 (b) and
D-RSV2-12 (b)).

Since the same day every validator has a view in every configuration, `x[i].view p`, a field of the
configuration rather than of the local state, and a delivery to a corrupted validator is a step of
the run, which files the message into its view and runs no protocol code
(`RealStsMulticastMultisetLog.Spec.Protocol`, section "Views").
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-- An infinite execution in real time: the configuration after each number of steps, the action
    taken at each step, and the real time at which each configuration is entered.

    `stamp i` is the real time at which configuration `i` is entered. So `stamp 0` is the start of
    the run, and `stamp (i + 1)` is the real time of step `i`, the step from configuration `i` to
    configuration `i + 1`. The real time never goes back (`mono`), never stops (`progress`), and
    starts at `0` (`init_stamp`). Several steps may share a stamp (`mono` is not strict): steps taken
    at one real time, in the order of the sequence.

    Read aloud: a sequence of configurations, each entered at a real time, each transition one of
    the system's steps; the real time of a step is the stamp of the configuration it enters.

    The labels are needed because fairness is a statement about which transitions occur (a tick is
    a transition of its own, and nothing in the step relation forces it to happen), and because
    the network's conditions on executions (`DeliveredBeforeActing`, `CatchUpAfterRestart`,
    `SyncedWithinBy`) speak of delivery steps: a restart keeps the view, and the view no longer
    tells a delivery after the restart from one before it.

    An alternative was to define occurrence from the relation itself
    (`Sys.Step a (cfg i) (cfg (i+1))`), which needs no field, but it only says an
    `a`-step *explains* the transition, not that it is the one taken — two actions
    with the same effect are then indistinguishable, and nothing can be counted. -/
structure Execution {St Lbl : Type} (Sys : System St Lbl) where
  /-- The configuration after `i` steps. -/
  cfg : Nat → St
  /-- The action taken at step `i`. -/
  lbl : Nat → Lbl
  /-- The real time at which configuration `i` is entered; for `i ≥ 1`, the real time of step
      `i − 1`. -/
  stamp : Nat → ℝ
  /-- It starts initial. -/
  init : Sys.Init (cfg 0)
  /-- Consecutive configurations are related by that action. -/
  step : ∀ i, Sys.Step (lbl i) (cfg i) (cfg (i + 1))
  /-- Real time never goes back: each configuration is entered no earlier than the one before. -/
  mono : ∀ i, stamp i ≤ stamp (i + 1)
  /-- Real time never stops: every real time `r` is reached by some configuration's stamp. -/
  progress : ∀ r : ℝ, ∃ i, r ≤ stamp i
  /-- The run starts at real time `0`. -/
  init_stamp : stamp 0 = 0

/-- `x[i]` is the configuration after `i` steps. Indexing is total, so the
    validity side-condition is trivial. -/
instance {St Lbl : Type} {Sys : System St Lbl} :
    GetElem (Execution Sys) Nat St (fun _ _ => True) where
  getElem x i _ := x.cfg i

/-- Configuration `i` of `x` is in force at the real time `s`: it was entered before `s`, and the
    step that leaves it is taken at `s` or later, `x.stamp i < s ≤ x.stamp (i + 1)`.

    The steps stamped `s` are taken from this configuration or from those after it; so the
    configuration in force at `s` is the one the real time `s` finds before any of its own steps. A
    configuration entered and left at one real time is in force at no real time. For every `s > 0`
    exactly one configuration is in force at `s` (from `mono`, `progress` and `init_stamp`).

    Read aloud: as the real time reaches `s`, `x[i]` is the configuration the run is in. -/
def Execution.InForce {St Lbl : Type} {Sys : System St Lbl} (x : Execution Sys) (i : Nat)
    (s : ℝ) : Prop :=
  x.stamp i < s ∧ s ≤ x.stamp (i + 1)

/-- Executions of a protocol. The environment's corruptions and crashes are in the
    configurations and the real time is in the stamps, so there is no schedule to parametrize
    by. -/
abbrev Exec {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) :=
  Execution (system Node Msg NodeState Ev Pr)

/-! ### Reading an execution

`x[i]` is the configuration after `i` steps, so `x[i].clock p` is what `p`'s clock reads there
(`some` integer, or `none` before the clock exists and from `p`'s corruption on), `x[i][p]` is `p`'s local state there (`some`
when known, `none` when unknown: before `p` first comes online, and from its corruption on),
`x[i].view p` is `p`'s view there (the signed messages delivered to `p` so far, whatever its local
state, a corrupted `p` included), and `x[i].crashed`, `x[i].adv` are the crashed set and the
corrupted set there.
`x.stamp i` is the real time configuration `i` is entered, and `x.stamp (i + 1)` the real time of
step `i`. `x.Honest i p` says `p` is outside the corrupted set there, and `x.Enabled i a` that the
action `a` may be taken at step `i`.

There is deliberately no `Active`: whether a validator is *participating* — as
opposed to merely up — is decided by its own program, so no framework-level
predicate can express it. Statements that need it take it as a parameter. -/

/-- Is `p` still honest after `i` steps? Corruption is a step of the run, so this is
    relative to the step.

    Read aloud: `p` is outside the corrupted set of configuration `i`. -/
def Execution.Honest {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) (p : Node) : Prop :=
  p ∉ x[i].adv


/-- Action `a` may be taken at step `i`.

    Read off the action's own `ActionSpec`, so it cannot disagree with the step
    relation, and `ActionSpec.feasible` guarantees it does not promise more than the
    effect delivers. An earlier version passed the enabling condition to `WeakFair`
    as a separate argument, with nothing tying the two together: a wrong one made the
    assumption either vacuous or unsatisfiable, and an unsatisfiable assumption makes
    every theorem under it vacuously true.

    Read aloud: `a`'s enabling condition holds of configuration `i`. -/
def Execution.Enabled {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) (a : Action Node Msg Ev) : Prop :=
  (spec Pr a).Enabled x[i]

end Framework.RealStsMulticastMultisetLog

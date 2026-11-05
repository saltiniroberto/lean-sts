module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Validator sets, their weights, and committees

What some conditions on executions (`RealStsMulticastMultisetLog.Spec.Conditions`) read besides an execution: the
validator set as a protocol has it at a block (`Registry`) and the weight arithmetic over it
(`counted`, `IsQuorum`, `quorumPairs`, `guaranteed`); a committee's specification
(`SleepinessWindow`, `CommitteeSpec`, and `CommitteeSpec.comap`, a committee read through a function of
what its members are computed from); and `MostOf`, a majority count over a set of validators.
None of them reads an execution, and the bare framework (`RealStsMulticastMultisetLog.Spec.Protocol`,
`RealStsMulticastMultisetLog.Spec.Execution`) reads none of them: a statement passes them to a condition as
parameters, the protocol's own.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-! ### The validator set and its weights -/

/-- The validator set as a protocol has it at a block. -/
structure Registry (Node : Type) where
  /-- Each validator's weight. -/
  weight : (v : Node) → ℕ
  /-- The validators entered and not exited. -/
  active : Finset Node
  /-- The slashed validators. -/
  slashed : Finset Node
  /-- The weight a quorum must reach. -/
  quorum : ℕ

/-- `counted reg S`: the weight of the validators of `S` that `reg` counts, active and not slashed.

Read aloud: the summed weight, in `reg`, of the members of `S` that are active and not slashed. -/
def counted {Node : Type} [DecidableEq Node] (reg : Registry Node) (S : Finset Node) : ℕ :=
  ∑ v ∈ S ∩ (reg.active \ reg.slashed), reg.weight v

/-- `S` is a quorum under `reg`: its counted weight reaches `reg`'s quorum.

Read aloud: `S` weighs, in `reg`, at least the quorum. -/
def IsQuorum {Node : Type} [DecidableEq Node] (reg : Registry Node) (S : Finset Node) : Prop :=
  reg.quorum ≤ counted reg S

instance {Node : Type} [DecidableEq Node] (reg : Registry Node) (S : Finset Node) :
    Decidable (IsQuorum reg S) :=
  Nat.decLe _ _

/-- The pairs of a quorum under `reg` and a quorum under `reg'`, drawn from the two active sets.

Read aloud: every pair of a quorum of `reg`'s active validators and a quorum of `reg'`'s. -/
def quorumPairs {Node : Type} [DecidableEq Node] (reg reg' : Registry Node) :
    Finset (Finset Node × Finset Node) :=
  (reg.active.powerset ×ˢ reg'.active.powerset).filter fun pair =>
    IsQuorum reg pair.1 ∧ IsQuorum reg' pair.2

/-- `guaranteed reg reg'`, written `I(reg, reg')`: the least weight, counted in `reg`, that a quorum
under `reg` and a quorum under `reg'` share; `0` when one of the two has no quorum.

Read aloud: the weight any quorum of `reg` and any quorum of `reg'` must have in common. -/
def guaranteed {Node : Type} [DecidableEq Node] (reg reg' : Registry Node) : ℕ :=
  if h : (quorumPairs reg reg').Nonempty then
    (quorumPairs reg reg').inf' h fun pair => counted reg (pair.1 ∩ pair.2)
  else 0

open Classical in
/-- Most of `S` satisfy `P`: the members of `S` that satisfy `P` outnumber those that do not.

Read aloud: more of `S` satisfy `P` than do not. -/
noncomputable def MostOf {Node : Type} (S : Finset Node) (P : (v : Node) → Prop) : Prop :=
  (S.filter fun v => ¬ P v).card < (S.filter P).card

/-! ### Committees -/

/-- A committee's sleepiness window `[tStart, tEnd]`: the real window through which a member must
stay up and honest to have done the committee's work. -/
structure SleepinessWindow where
  /-- The start of the sleepiness window. -/
  tStart : ℝ
  /-- The end of the sleepiness window. -/
  tEnd : ℝ

/-- A protocol's specification of one committee, its members computed from `NodeInfo`, what is read
of a node's state. -/
structure CommitteeSpec (Node NodeInfo : Type) where
  /-- `members info`: the committee's members as a node computes them from `info`, what is read of
  its state. -/
  members : (info : NodeInfo) → Finset Node
  /-- The committee's sleepiness window. -/
  sleepinessWindow : SleepinessWindow
  /-- The time until which the committee needs the network synchronous to work as designed. -/
  tSyncNeededUntil : ℝ

/-- `committee.comap f`: the committee `committee` with its members computed from `f l`, what `f`
reads of `l`; its sleepiness window and the time until which it needs synchrony are `committee`'s.

Read aloud: the same committee, its members computed from `l` through `f`. -/
def CommitteeSpec.comap {Node NodeInfo L : Type} (f : (l : L) → NodeInfo)
    (committee : CommitteeSpec Node NodeInfo) : CommitteeSpec Node L where
  members l := committee.members (f l)
  sleepinessWindow := committee.sleepinessWindow
  tSyncNeededUntil := committee.tSyncNeededUntil

end Framework.RealStsMulticastMultisetLog

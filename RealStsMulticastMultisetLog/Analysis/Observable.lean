module
public import RealStsMulticastMultisetLog.Spec.Conditions
public import RealStsMulticastMultisetLog.Analysis.ObservableSimpAttr

@[expose] public section

/-!
# The conditions on executions, written over `Observable`: what they say on a run and on the run as observed

Theorems about the definitions of `RealStsMulticastMultisetLog.Spec.Observable` and
`RealStsMulticastMultisetLog.Spec.Conditions`, kept out of the specification so that it reads as
definitions only. No condition on executions is assumed, and nothing here is part of the bare
framework.

* **The readings of a run.** For each field of `Observable`, a lemma that on a run `x : Exec Pr` the
  reading is the run's own (`Observable.stamp x i = x.stamp i`, …), by `rfl`, in the simp set
  `observable_exec` and in the default simp set. A proof that takes apart a hypothesis of a
  condition over `Exec Pr` sees the class's readings; `dsimp only [observable_exec] at h` turns them
  back into the run's own.
* **On a run, each name over `Exec Pr` is the definition over the class.** For each definition of
  `RealStsMulticastMultisetLog.Spec.Conditions` written once over `Observable`, the theorem `…_iff`
  states that on a run `x : Exec Pr` the name over `Exec Pr` is that definition at `x`, a parameter
  that reads a node's memory state `st` passed to it as `fun l => … l.st`, and the tree of a node
  read through the class `BlockTree` (the run form passed `BlockTree.tree`) and the validator set at
  a block read through the class `BlockRegistry` (the run form passed `BlockRegistry.registry`), and
  a message's author and inclusions read through the class `MessageAuthorship` (the run form passed
  `MessageAuthorship.author` and `MessageAuthorship.carries`). Each is `Iff.rfl`, from the name's
  definition, except `weightBounds_iff`, which goes field by field: `WeightBounds` and
  `WeightBoundsG` are two structures.
* **On a run as observed.** For each generic definition, what it says on `observe f x` is what it
  says on `x` (`…_observe`); a parameter that reads a node's state is read through `f` on the run, a
  node's tree is the same on the observed run and on the run when `f` keeps it, a parameter `acting`
  is taken as two, one on observed runs and one on runs, that agree, and the committees, which
  neither an observed run nor a run carries, are given to both through
  `ObservableWithCommittees.ofCommittees`.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

open Observable

/-! ### The readings of a run -/

section Readings
variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr)

/-- On a run, the action of step `j` the class reads is the run's own. -/
@[simp, observable_exec] theorem observable_lbl_exec (j : Nat) : lbl x j = x.lbl j := rfl

/-- On a run, the real time configuration `i` is entered, as the class reads it, is the run's
    own. -/
@[simp, observable_exec] theorem observable_stamp_exec (i : Nat) : stamp x i = x.stamp i := rfl

/-- On a run, node `p`'s clock in configuration `i`, as the class reads it, is the run's own. -/
@[simp, observable_exec] theorem observable_clock_exec (i : Nat) (p : Node) :
    clock x i p = x[i].clock p := rfl

/-- On a run, node `p`'s state in configuration `i`, as the class reads it, is its local state. -/
@[simp, observable_exec] theorem observable_state_exec (i : Nat) (p : Node) :
    state x i p = x[i][p] := rfl

/-- On a run, node `p`'s view in configuration `i`, as the class reads it, is the run's own. -/
@[simp, observable_exec] theorem observable_view_exec (i : Nat) (p : Node) :
    view x i p = x[i].view p := rfl

/-- On a run, the envelopes sent up to configuration `i`, as the class reads them, are the run's
    own. -/
@[simp, observable_exec] theorem observable_sent_exec (i : Nat) : sent x i = x[i].sent := rfl

/-- On a run, the corrupted set of configuration `i`, as the class reads it, is the run's own. -/
@[simp, observable_exec] theorem observable_adv_exec (i : Nat) : adv x i = x[i].adv := rfl

/-- On a run, the crashed set of configuration `i`, as the class reads it, is the run's own. -/
@[simp, observable_exec] theorem observable_crashed_exec (i : Nat) :
    crashed x i = x[i].crashed := rfl

end Readings

/-! ### On a run, each name over `Exec Pr` is the definition over the class -/

/-- On a run, `NoCrashDuring` is `NoCrashDuringG`, by definition. -/
theorem noCrashDuring_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) :
    NoCrashDuring x ↔
      NoCrashDuringG x :=
  Iff.rfl

/-- On a run, `ClockWithinSkewR` is `ClockWithinSkew`, by definition. -/
theorem clockWithinSkewR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockAhead ΔClockBehind : ℝ) (x : Exec Pr) :
    ClockWithinSkewR ΔClockAhead ΔClockBehind x ↔
      ClockWithinSkew ΔClockAhead ΔClockBehind x :=
  Iff.rfl

/-- On a run, `ClockNotAheadR` is `ClockNotAhead`, by definition. -/
theorem clockNotAheadR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockBehind : ℝ) (x : Exec Pr) :
    ClockNotAheadR ΔClockBehind x ↔
      ClockNotAhead ΔClockBehind x :=
  Iff.rfl

/-- On a run, `ClockAtTimeR` is `ClockAtTime`, by definition. -/
theorem clockAtTimeR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) :
    ClockAtTimeR x ↔
      ClockAtTime x :=
  Iff.rfl

/-- On a run, `ClockAdvancesWithinR` is `ClockAdvancesWithin`, by definition. -/
theorem clockAdvancesWithinR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockAhead ΔClockBehind : ℝ) (x : Exec Pr) :
    ClockAdvancesWithinR ΔClockAhead ΔClockBehind x ↔
      ClockAdvancesWithin ΔClockAhead ΔClockBehind x :=
  Iff.rfl

/-- Under `ClockWithinSkew`, `ClockAdvancesWithin` gives back the case with the real-time bounds:
    the step that sets the clock to `t` is at a real time in `[t − ΔClockAhead, t + ΔClockBehind]`.
    Both are conditions on executions, which no step of the bare framework reads.

    Read aloud: if every step `setClock p t` is at a real time in `[t − ΔClockAhead,
    t + ΔClockBehind]`, and the clock condition `ClockAdvancesWithin` holds, then whenever a node
    `p` is up, not corrupted, and its clock reads less than a reading `t`, either some step `j` sets
    `p`'s clock to `t` at a real time `stamp x (j + 1)` in that interval, or `p` crashes or is
    corrupted after configuration `i`, by the real time `t + ΔClockBehind`. -/
theorem clockAdvancesWithin_bounded {X Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    [Observable X Node Msg L Ev] {ΔClockAhead ΔClockBehind : ℝ} {x : X}
    (hSkew : ClockWithinSkew ΔClockAhead ΔClockBehind x)
    (hAdv : ClockAdvancesWithin ΔClockAhead ΔClockBehind x) :
    ∀ (t : Time) (p : Node) (i : Nat) (t' : Time),
      p ∉ crashed x i → state x i p ≠ none → p ∉ adv x i → clock x i p = some t' → t' < t →
        (∃ j : Nat, lbl x j = .setClock p t ∧
          (t : ℝ) - ΔClockAhead ≤ stamp x (j + 1) ∧ stamp x (j + 1) ≤ t + ΔClockBehind) ∨
        (∃ j : Nat, i < j ∧ stamp x j ≤ t + ΔClockBehind ∧ (p ∈ crashed x j ∨ p ∈ adv x j)) := by
  intro t p i t' h1 h2 h3 h4 h5
  rcases hAdv t p i t' h1 h2 h3 h4 h5 with ⟨j, hj⟩ | hc
  · exact Or.inl ⟨j, hj, hSkew j p t hj⟩
  · exact Or.inr hc

/-- On a run, `TicksWithinR` is `TicksWithin`, by definition. -/
theorem ticksWithinR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockBehind : ℝ) (x : Exec Pr) :
    TicksWithinR ΔClockBehind x ↔
      TicksWithin ΔClockBehind x :=
  Iff.rfl

/-- On a run, `ActsWithinSkew` is `ActsWithinSkewG`, by definition. -/
theorem actsWithinSkew_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockBehind : ℝ) (x : Exec Pr) :
    ActsWithinSkew ΔClockBehind x ↔
      ActsWithinSkewG ΔClockBehind x :=
  Iff.rfl

/-- On a run, `DiligentWithinR` is `DiligentWithin`, by definition. -/
theorem diligentWithinR_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockAhead ΔClockBehind : ℝ) (x : Exec Pr) :
    DiligentWithinR ΔClockAhead ΔClockBehind x ↔
      DiligentWithin ΔClockAhead ΔClockBehind x :=
  Iff.rfl

/-- On a run, `Execution.ActingStep` is `ActingStepG`, by definition. -/
theorem Execution.actingStep_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (k : Nat) (p : Node) :
    Execution.ActingStep x k p ↔
      ActingStepG x k p :=
  Iff.rfl

/-- On a run, `TickStep` is `TickStepG`, by definition. -/
theorem tickStep_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (k : Nat) (p : Node) :
    TickStep x k p ↔
      TickStepG x k p :=
  Iff.rfl

/-- On a run, `Execution.UpBetween` is `UpBetweenG`, by definition. -/
theorem Execution.upBetween_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i k : Nat) (p : Node) :
    Execution.UpBetween x i k p ↔
      UpBetweenG x i k p :=
  Iff.rfl

/-- On a run, `Execution.UpAndHonestThroughout` is `UpAndHonestThroughoutG`, by definition. -/
theorem Execution.upAndHonestThroughout_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (t t' : ℝ) (p : Node) :
    Execution.UpAndHonestThroughout x t t' p ↔
      UpAndHonestThroughoutG x t t' p :=
  Iff.rfl

/-- On a run, `Execution.UpAndHonestUntilActing` is `UpAndHonestUntilActingG`, by definition. -/
theorem Execution.upAndHonestUntilActing_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (acting : Exec Pr → Nat → Node → Prop)
    (x : Exec Pr) (t t' : ℝ) (p : Node) :
    Execution.UpAndHonestUntilActing acting x t t' p ↔
      UpAndHonestUntilActingG acting x t t' p :=
  Iff.rfl

/-- On a run, `DueBy` is `DueByG`, by definition. -/
theorem dueBy_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (dl : (m : Msg) → (tSend : ℝ) → ℝ) (x : Exec Pr) (i : Nat)
    (e : Envelope Node Msg) (t : ℝ) :
    DueBy dl x i e t ↔
      DueByG dl x i e t :=
  Iff.rfl

/-- On a run, `DeliveredBeforeActing` is `DeliveredBeforeActingG`, by definition. -/
theorem deliveredBeforeActing_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (acting : Exec Pr → Nat → Node → Prop)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) (x : Exec Pr) :
    DeliveredBeforeActing acting dl x ↔
      DeliveredBeforeActingG acting dl x :=
  Iff.rfl

/-- On a run, `CatchUpAfterRestart` is `CatchUpAfterRestartG`, by definition. -/
theorem catchUpAfterRestart_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (acting : Exec Pr → Nat → Node → Prop)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) (dlW : (m : Msg) → (tRestart : ℝ) → ℝ) (x : Exec Pr) :
    CatchUpAfterRestart acting dl dlW x ↔
      CatchUpAfterRestartG acting dl dlW x :=
  Iff.rfl

/-- On a run, `SyncedWithinBy` is `SyncedWithinByG`, by definition. -/
theorem syncedWithinBy_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (acting : Exec Pr → Nat → Node → Prop)
    (serves : (tClock : Time) → (st : NodeState) → (m : Msg) → Prop)
    (sync : (m : Msg) → (t : ℝ) → ℝ) (x : Exec Pr) :
    SyncedWithinBy acting serves sync x ↔
      SyncedWithinByG acting (fun tClock l m => serves tClock l.st m) sync x :=
  Iff.rfl

/-- On a run, `TickOncePerReading` is `TickOncePerReadingG`, by definition. -/
theorem tickOncePerReading_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) :
    TickOncePerReading x ↔
      TickOncePerReadingG x :=
  Iff.rfl

/-- On a run, with messages read through a `MessageAuthorship`, `UnforgeableSends` reading the
    authors `MessageAuthorship.author` and the inclusions `MessageAuthorship.carries` is
    `UnforgeableSendsG`, by definition. -/
theorem unforgeableSends_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    [MessageAuthorship Msg Node] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) :
    UnforgeableSends MessageAuthorship.author MessageAuthorship.carries x ↔
      UnforgeableSendsG x :=
  Iff.rfl

/-- On a run of a protocol whose memory states have a `BlockTree`, `Execution.InHonestTreeBy`
    reading the tree `BlockTree.tree` is `InHonestTreeByG`, by definition. -/
theorem Execution.inHonestTreeBy_iff {Node Msg NodeState Ev Block : Type} [DecidableEq Node]
    [DecidableEq Msg] [BlockTree NodeState Block] {Pr : Protocol Node Msg NodeState Ev}
    (x : Exec Pr) (tBy : ℝ) (B : Block) :
    Execution.InHonestTreeBy x BlockTree.tree tBy B ↔ InHonestTreeByG x tBy B :=
  Iff.rfl

/-- On a run, `Execution.HonestSentBy` is `HonestSentByG`, by definition. -/
theorem Execution.honestSentBy_iff {Node Msg NodeState Ev Block : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr)
    (blockOf : (m : Msg) → Option Block) (tBy : ℝ) (B : Block) :
    Execution.HonestSentBy x blockOf tBy B ↔
      HonestSentByG x blockOf tBy B :=
  Iff.rfl

/-- On a run, `AdversaryUnderIntersectionBy` is `AdversaryUnderIntersectionByG`, by definition. -/
theorem adversaryUnderIntersectionBy_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (reg reg' : Registry Node) (tBy : ℝ)
    (x : Exec Pr) :
    AdversaryUnderIntersectionBy reg reg' tBy x ↔
      AdversaryUnderIntersectionByG reg reg' tBy x :=
  Iff.rfl

/-- On a run, `AdversaryUnderQuorumBy` is `AdversaryUnderQuorumByG`, by definition. -/
theorem adversaryUnderQuorumBy_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (reg : Registry Node) (tBy : ℝ)
    (x : Exec Pr) :
    AdversaryUnderQuorumBy reg tBy x ↔
      AdversaryUnderQuorumByG reg tBy x :=
  Iff.rfl

/-- On a run of a protocol whose memory states have a `BlockTree` and whose blocks have a
    `BlockRegistry`, `WeightBounds` reading the tree `BlockTree.tree` and the validator sets
    `BlockRegistry.registry` holds exactly when `WeightBoundsG` does: each field of one is the same
    field of the other, by definition. -/
theorem weightBounds_iff {Node Msg NodeState Ev Block : Type} [DecidableEq Node] [DecidableEq Msg]
    [BlockTree NodeState Block] [BlockRegistry Block Node] {Pr : Protocol Node Msg NodeState Ev}
    (tAwakeEnd : ℝ) (x : Exec Pr) :
    WeightBounds BlockTree.tree BlockRegistry.registry tAwakeEnd x ↔ WeightBoundsG tAwakeEnd x :=
  ⟨fun h => ⟨h.third, h.quorum⟩, fun h => ⟨h.third, h.quorum⟩⟩

/-- On a run, `HealingPhase` is `HealingPhaseG`, by definition. -/
theorem healingPhase_iff {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (tGST tGAT tAwakeEnd : ℝ) (x : Exec Pr) :
    HealingPhase tGST tGAT tAwakeEnd x ↔
      HealingPhaseG tGST tGAT tAwakeEnd x :=
  Iff.rfl

/-- On a run, `Execution.MostOfCommittee` is `MostOfCommitteeG`, by definition. -/
theorem Execution.mostOfCommittee_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr)
    (committee : CommitteeSpec Node NodeState) (P : (v : Node) → Prop) :
    Execution.MostOfCommittee x committee P ↔
      MostOfCommitteeG x (committee.comap fun l => l.st) P :=
  Iff.rfl

/-- On a run, `CommitteeSleepinessFrom` is `CommitteeSleepinessFromG` at the run read with the
    committees through `ObservableWithCommittees.ofCommittees`, by definition. -/
theorem committeeSleepinessFrom_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev}
    (committees : (ci : Nat) → CommitteeSpec Node NodeState) (tFrom : ℝ) (x : Exec Pr) :
    CommitteeSleepinessFrom committees tFrom x ↔
      @CommitteeSleepinessFromG (Exec Pr) Node Msg (Local Node Msg NodeState) Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ ci => (committees ci).comap fun l => l.st) tFrom x :=
  Iff.rfl

/-- On a run, `AsyncPeriodSleepiness` is `AsyncPeriodSleepinessG` at the run read with the
    committees through `ObservableWithCommittees.ofCommittees`, by definition. -/
theorem asyncPeriodSleepiness_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev}
    (committees : (ci : Nat) → CommitteeSpec Node NodeState)
    (tPreAsync ΔPreAsync tAsyncStart tAsyncEnd ΔRecovery : ℝ) (x : Exec Pr) :
    AsyncPeriodSleepiness committees tPreAsync ΔPreAsync tAsyncStart tAsyncEnd ΔRecovery x ↔
      @AsyncPeriodSleepinessG (Exec Pr) Node Msg (Local Node Msg NodeState) Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ ci => (committees ci).comap fun l => l.st) tPreAsync
        ΔPreAsync tAsyncStart tAsyncEnd ΔRecovery x :=
  Iff.rfl

/-- On a run, `HonestProposerThrough` is `HonestProposerThroughG`, by definition. -/
theorem honestProposerThrough_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (tAwakeEnd tPreAsync tProposalStart : ℝ)
    (vProposer : Node) (x : Exec Pr) :
    HonestProposerThrough tAwakeEnd tPreAsync tProposalStart vProposer x ↔
      HonestProposerThroughG tAwakeEnd tPreAsync tProposalStart vProposer x :=
  Iff.rfl

/-! ### On a run as observed

`observe f x` has the run's actions, stamps, clocks, views, sent envelopes, corrupted and crashed
sets, and `f l` where the run has the local state `l`. So a condition that does not read a node's
state says the same on a run as observed as on the run, by definition; one that reads only whether
the state is known says the same too; and one with a parameter reading the state says on the
observed run, with a parameter over `V`, what it says on the run with that parameter read through
`f`. A condition with a parameter `acting` says on the observed run what it says on the run when the
two `acting` agree on `x` as observed and on `x`. -/

section Observe

variable {Node Msg NodeState Ev V : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (f : Local Node Msg NodeState → V) (x : Exec Pr)

/-! #### The readings -/

/-- A run as observed has the run's actions. -/
@[simp] theorem lbl_observe (j : Nat) : lbl (observe f x) j = lbl x j := rfl

/-- A run as observed has the run's stamps. -/
@[simp] theorem stamp_observe (i : Nat) : stamp (observe f x) i = stamp x i := rfl

/-- A run as observed has the run's clocks. -/
@[simp] theorem clock_observe (i : Nat) (p : Node) : clock (observe f x) i p = clock x i p := rfl

/-- On a run as observed, a node's state is the image under `f` of its local state on the run. -/
@[simp] theorem state_observe (i : Nat) (p : Node) :
    state (observe f x) i p = (state x i p).map f := rfl

/-- A run as observed has the run's views. -/
@[simp] theorem view_observe (i : Nat) (p : Node) : view (observe f x) i p = view x i p := rfl

/-- A run as observed has the run's sent envelopes. -/
@[simp] theorem sent_observe (i : Nat) : sent (observe f x) i = sent x i := rfl

/-- A run as observed has the run's corrupted sets. -/
@[simp] theorem adv_observe (i : Nat) : adv (observe f x) i = adv x i := rfl

/-- A run as observed has the run's crashed sets. -/
@[simp] theorem crashed_observe (i : Nat) : crashed (observe f x) i = crashed x i := rfl

/-- On a run as observed a node's state is known exactly when its local state is known on the
    run. -/
theorem state_observe_ne_none (i : Nat) (p : Node) :
    state (observe f x) i p ≠ none ↔ state x i p ≠ none := by
  simp only [state_observe, ne_eq, Option.map_eq_none_iff]

/-- `HonestG` on a run as observed is `HonestG` on the run. -/
theorem honestG_observe (i : Nat) (p : Node) : HonestG (observe f x) i p ↔ HonestG x i p :=
  Iff.rfl

/-- `InForceG` on a run as observed is `InForceG` on the run. -/
theorem inForceG_observe (i : Nat) (s : ℝ) : InForceG (observe f x) i s ↔ InForceG x i s :=
  Iff.rfl

/-! #### The conditions and readings of `RealStsMulticastMultisetLog.Spec.Conditions` -/

/-- `NoCrashDuringG` on a run as observed is `NoCrashDuringG` on the run. -/
theorem noCrashDuringG_observe : NoCrashDuringG (observe f x) ↔ NoCrashDuringG x :=
  Iff.rfl

/-- `ClockWithinSkew` on a run as observed is `ClockWithinSkew` on the run. -/
theorem clockWithinSkew_observe (ΔClockAhead ΔClockBehind : ℝ) :
    ClockWithinSkew ΔClockAhead ΔClockBehind (observe f x) ↔
      ClockWithinSkew ΔClockAhead ΔClockBehind x :=
  Iff.rfl

/-- `ClockNotAhead` on a run as observed is `ClockNotAhead` on the run. -/
theorem clockNotAhead_observe (ΔClockBehind : ℝ) :
    ClockNotAhead ΔClockBehind (observe f x) ↔ ClockNotAhead ΔClockBehind x :=
  Iff.rfl

/-- `ClockAtTime` on a run as observed is `ClockAtTime` on the run. -/
theorem clockAtTime_observe : ClockAtTime (observe f x) ↔ ClockAtTime x :=
  Iff.rfl

/-- `ClockAdvancesWithin` on a run as observed is `ClockAdvancesWithin` on the run. -/
theorem clockAdvancesWithin_observe (ΔClockAhead ΔClockBehind : ℝ) :
    ClockAdvancesWithin ΔClockAhead ΔClockBehind (observe f x) ↔
      ClockAdvancesWithin ΔClockAhead ΔClockBehind x := by
  unfold ClockAdvancesWithin
  simp only [state_observe_ne_none]
  exact Iff.rfl

/-- `TicksWithin` on a run as observed is `TicksWithin` on the run. -/
theorem ticksWithin_observe (ΔClockBehind : ℝ) :
    TicksWithin ΔClockBehind (observe f x) ↔ TicksWithin ΔClockBehind x := by
  unfold TicksWithin
  simp only [state_observe_ne_none]
  exact Iff.rfl

/-- `ActsWithinSkewG` on a run as observed is `ActsWithinSkewG` on the run. -/
theorem actsWithinSkewG_observe (ΔClockBehind : ℝ) :
    ActsWithinSkewG ΔClockBehind (observe f x) ↔ ActsWithinSkewG ΔClockBehind x :=
  Iff.rfl

/-- `DiligentWithin` on a run as observed is `DiligentWithin` on the run. -/
theorem diligentWithin_observe (ΔClockAhead ΔClockBehind : ℝ) :
    DiligentWithin ΔClockAhead ΔClockBehind (observe f x) ↔
      DiligentWithin ΔClockAhead ΔClockBehind x :=
  and_congr (clockAdvancesWithin_observe f x _ _) (ticksWithin_observe f x _)

/-- `ActingStepG` on a run as observed is `ActingStepG` on the run. -/
theorem actingStepG_observe (k : Nat) (p : Node) :
    ActingStepG (observe f x) k p ↔ ActingStepG x k p :=
  Iff.rfl

/-- `TickStepG` on a run as observed is `TickStepG` on the run. -/
theorem tickStepG_observe (k : Nat) (p : Node) : TickStepG (observe f x) k p ↔ TickStepG x k p :=
  Iff.rfl

/-- `UpBetweenG` on a run as observed is `UpBetweenG` on the run. -/
theorem upBetweenG_observe (i k : Nat) (p : Node) :
    UpBetweenG (observe f x) i k p ↔ UpBetweenG x i k p := by
  unfold UpBetweenG
  simp only [state_observe_ne_none]
  exact Iff.rfl

/-- `UpAndHonestThroughoutG` on a run as observed is `UpAndHonestThroughoutG` on the run. -/
theorem upAndHonestThroughoutG_observe (t t' : ℝ) (p : Node) :
    UpAndHonestThroughoutG (observe f x) t t' p ↔ UpAndHonestThroughoutG x t t' p := by
  unfold UpAndHonestThroughoutG
  simp only [state_observe_ne_none]
  exact Iff.rfl

/-- `UpAndHonestUntilActingG` on a run as observed is `UpAndHonestUntilActingG` on the run, when the
    acting steps read on the observed run (`actingT`) are those read on the run (`actingR`). -/
theorem upAndHonestUntilActingG_observe (actingT : ObservedRun Node Msg Ev V → Nat → Node → Prop)
    (actingR : Exec Pr → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingT (observe f x) k p ↔ actingR x k p)
    (t t' : ℝ) (p : Node) :
    UpAndHonestUntilActingG actingT (observe f x) t t' p ↔
      UpAndHonestUntilActingG actingR x t t' p := by
  unfold UpAndHonestUntilActingG
  simp only [hacting, state_observe_ne_none]
  exact Iff.rfl

/-- `DueByG` on a run as observed is `DueByG` on the run. -/
theorem dueByG_observe (dl : (m : Msg) → (tSend : ℝ) → ℝ) (i : Nat) (e : Envelope Node Msg)
    (t : ℝ) : DueByG dl (observe f x) i e t ↔ DueByG dl x i e t :=
  Iff.rfl

/-- `DeliveredBeforeActingG` on a run as observed is `DeliveredBeforeActingG` on the run, when the
    acting steps read on the observed run (`actingT`) are those read on the run (`actingR`). -/
theorem deliveredBeforeActingG_observe (actingT : ObservedRun Node Msg Ev V → Nat → Node → Prop)
    (actingR : Exec Pr → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingT (observe f x) k p ↔ actingR x k p)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) :
    DeliveredBeforeActingG actingT dl (observe f x) ↔ DeliveredBeforeActingG actingR dl x := by
  unfold DeliveredBeforeActingG
  simp only [hacting, upBetweenG_observe]
  exact Iff.rfl

/-- `CatchUpAfterRestartG` on a run as observed is `CatchUpAfterRestartG` on the run, when the
    acting steps read on the observed run (`actingT`) are those read on the run (`actingR`). -/
theorem catchUpAfterRestartG_observe (actingT : ObservedRun Node Msg Ev V → Nat → Node → Prop)
    (actingR : Exec Pr → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingT (observe f x) k p ↔ actingR x k p)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) (dlW : (m : Msg) → (tRestart : ℝ) → ℝ) :
    CatchUpAfterRestartG actingT dl dlW (observe f x) ↔ CatchUpAfterRestartG actingR dl dlW x := by
  unfold CatchUpAfterRestartG
  simp only [hacting]
  exact Iff.rfl

/-- `SyncedWithinByG` on a run as observed, with `serves` reading a node's value `V`, is
    `SyncedWithinByG` on the run with `serves` read through `f`, when the acting steps read on the
    observed run (`actingT`) are those read on the run (`actingR`). -/
theorem syncedWithinByG_observe (actingT : ObservedRun Node Msg Ev V → Nat → Node → Prop)
    (actingR : Exec Pr → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingT (observe f x) k p ↔ actingR x k p)
    (serves : (tClock : Time) → (v : V) → (m : Msg) → Prop) (sync : (m : Msg) → (t : ℝ) → ℝ) :
    SyncedWithinByG actingT serves sync (observe f x) ↔
      SyncedWithinByG actingR (fun tClock l m => serves tClock (f l) m) sync x := by
  unfold SyncedWithinByG
  simp only [upAndHonestUntilActingG_observe f x actingT actingR hacting, hacting, state_observe,
    Option.map_eq_some_iff, ne_eq, Option.map_eq_none_iff]
  constructor
  · intro h t i p p' m tClock l hin hcr hh hl hclk hserv hup
    rcases h t i p p' m tClock (f l) hin hcr hh ⟨l, hl, rfl⟩ hclk hserv hup with
      ⟨tClock'', _, ⟨l'', hl'', rfl⟩, hclk'', hserv''⟩ |
      ⟨j, i', e, tClock', l', hij, hst, ⟨l'', hl'', rfl⟩, hclk', hserv', hrest⟩
    · exact Or.inl ⟨tClock'', l'', hl'', hclk'', hserv''⟩
    · exact Or.inr ⟨j, i', e, tClock', l'', hij, hst, hl'', hclk', hserv', hrest⟩
  · rintro h t i p p' m tClock _ hin hcr hh ⟨l, hl, rfl⟩ hclk hserv hup
    rcases h t i p p' m tClock l hin hcr hh hl hclk hserv hup with
      ⟨tClock'', l'', hl'', hclk'', hserv''⟩ |
      ⟨j, i', e, tClock', l', hij, hst, hl', hclk', hserv', hrest⟩
    · exact Or.inl ⟨tClock'', f l'', ⟨l'', hl'', rfl⟩, hclk'', hserv''⟩
    · exact Or.inr ⟨j, i', e, tClock', f l', hij, hst, ⟨l', hl', rfl⟩, hclk', hserv', hrest⟩

/-- `TickOncePerReadingG` on a run as observed is `TickOncePerReadingG` on the run. -/
theorem tickOncePerReadingG_observe : TickOncePerReadingG (observe f x) ↔ TickOncePerReadingG x :=
  Iff.rfl

/-- `UnforgeableSendsG` on a run as observed is `UnforgeableSendsG` on the run. -/
theorem unforgeableSendsG_observe [MessageAuthorship Msg Node] :
    UnforgeableSendsG (observe f x) ↔ UnforgeableSendsG x :=
  Iff.rfl

/-- `InHonestTreeByG` on a run as observed is `InHonestTreeByG` on the run, when `f` keeps the
    tree: the tree of `f l` is the tree of the memory state `l.st`. -/
theorem inHonestTreeByG_observe {Block : Type} [BlockTree V Block] [BlockTree NodeState Block]
    (hf : ∀ l : Local Node Msg NodeState, BlockTree.tree (f l) = BlockTree.tree l.st) (tBy : ℝ)
    (B : Block) :
    InHonestTreeByG (observe f x) tBy B ↔ InHonestTreeByG x tBy B := by
  unfold InHonestTreeByG
  simp only [state_observe, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, v, _, ⟨l, hl, rfl⟩, hh, ht, hB⟩
    rw [hf l] at hB
    exact ⟨i, v, l, hl, hh, ht, hB⟩
  · rintro ⟨i, v, l, hl, hh, ht, hB⟩
    refine ⟨i, v, f l, ⟨l, hl, rfl⟩, hh, ht, ?_⟩
    rw [hf l]
    exact hB

/-- `HonestSentByG` on a run as observed is `HonestSentByG` on the run. -/
theorem honestSentByG_observe {Block : Type} (blockOf : (m : Msg) → Option Block) (tBy : ℝ)
    (B : Block) : HonestSentByG (observe f x) blockOf tBy B ↔ HonestSentByG x blockOf tBy B :=
  Iff.rfl

/-- `AdversaryUnderIntersectionByG` on a run as observed is `AdversaryUnderIntersectionByG` on the
    run. -/
theorem adversaryUnderIntersectionByG_observe (reg reg' : Registry Node) (tBy : ℝ) :
    AdversaryUnderIntersectionByG reg reg' tBy (observe f x) ↔
      AdversaryUnderIntersectionByG reg reg' tBy x :=
  Iff.rfl

/-- `AdversaryUnderQuorumByG` on a run as observed is `AdversaryUnderQuorumByG` on the run. -/
theorem adversaryUnderQuorumByG_observe (reg : Registry Node) (tBy : ℝ) :
    AdversaryUnderQuorumByG reg tBy (observe f x) ↔ AdversaryUnderQuorumByG reg tBy x :=
  Iff.rfl

/-- `WeightBoundsG` on a run as observed is `WeightBoundsG` on the run, when `f` keeps the tree:
    the tree of `f l` is the tree of the memory state `l.st`. -/
theorem weightBoundsG_observe {Block : Type} [BlockTree V Block] [BlockTree NodeState Block]
    [BlockRegistry Block Node]
    (hf : ∀ l : Local Node Msg NodeState, BlockTree.tree (f l) = BlockTree.tree l.st)
    (tAwakeEnd : ℝ) :
    WeightBoundsG tAwakeEnd (observe f x) ↔ WeightBoundsG tAwakeEnd x := by
  constructor
  · rintro ⟨h3, hq⟩
    exact ⟨fun B B' hB hB' => h3 B B' ((inHonestTreeByG_observe f x hf _ B).2 hB)
        ((inHonestTreeByG_observe f x hf _ B').2 hB'),
      fun t B hB => hq t B ((inHonestTreeByG_observe f x hf t B).2 hB)⟩
  · rintro ⟨h3, hq⟩
    exact ⟨fun B B' hB hB' => h3 B B' ((inHonestTreeByG_observe f x hf _ B).1 hB)
        ((inHonestTreeByG_observe f x hf _ B').1 hB'),
      fun t B hB => hq t B ((inHonestTreeByG_observe f x hf t B).1 hB)⟩

/-- `HealingPhaseG` on a run as observed is `HealingPhaseG` on the run. -/
theorem healingPhaseG_observe (tGST tGAT tAwakeEnd : ℝ) :
    HealingPhaseG tGST tGAT tAwakeEnd (observe f x) ↔ HealingPhaseG tGST tGAT tAwakeEnd x := by
  unfold HealingPhaseG
  simp only [state_observe_ne_none]
  exact Iff.rfl

/-- `MostOfCommitteeG` on a run as observed, with the committee's members computed from a node's
    value `V`, is `MostOfCommitteeG` on the run with the committee read through `f`. -/
theorem mostOfCommitteeG_observe (committee : CommitteeSpec Node V) (P : (v : Node) → Prop) :
    MostOfCommitteeG (observe f x) committee P ↔
      MostOfCommitteeG x (committee.comap f) P := by
  unfold MostOfCommitteeG
  simp only [state_observe, Option.map_eq_some_iff]
  constructor
  · intro h v i l hl hh h1 h2
    exact h v i (f l) ⟨l, hl, rfl⟩ hh h1 h2
  · rintro h v i _ ⟨l, hl, rfl⟩ hh h1 h2
    exact h v i l hl hh h1 h2

/-- `CommitteeSleepinessFromG` on a run as observed read with the committees `committees`, their
    members computed from a node's value `V`, is `CommitteeSleepinessFromG` on the run read with
    each committee read through `f` (both read through `ObservableWithCommittees.ofCommittees`). -/
theorem committeeSleepinessFromG_observe (committees : (ci : Nat) → CommitteeSpec Node V)
    (tFrom : ℝ) :
    @CommitteeSleepinessFromG (ObservedRun Node Msg Ev V) Node Msg V Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ => committees) tFrom (observe f x) ↔
      @CommitteeSleepinessFromG (Exec Pr) Node Msg (Local Node Msg NodeState) Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ ci => (committees ci).comap f) tFrom x := by
  unfold CommitteeSleepinessFromG
  simp only [upAndHonestThroughoutG_observe, mostOfCommitteeG_observe]
  exact Iff.rfl

/-- `AsyncPeriodSleepinessG` on a run as observed read with the committees `committees`, their
    members computed from a node's value `V`, is `AsyncPeriodSleepinessG` on the run read with each
    committee read through `f` (both read through `ObservableWithCommittees.ofCommittees`). -/
theorem asyncPeriodSleepinessG_observe (committees : (ci : Nat) → CommitteeSpec Node V)
    (tPreAsync ΔPreAsync tAsyncStart tAsyncEnd ΔRecovery : ℝ) :
    @AsyncPeriodSleepinessG (ObservedRun Node Msg Ev V) Node Msg V Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ => committees) tPreAsync ΔPreAsync tAsyncStart
        tAsyncEnd ΔRecovery (observe f x) ↔
      @AsyncPeriodSleepinessG (Exec Pr) Node Msg (Local Node Msg NodeState) Ev _ _
        (ObservableWithCommittees.ofCommittees fun _ ci => (committees ci).comap f) tPreAsync ΔPreAsync
        tAsyncStart tAsyncEnd ΔRecovery x := by
  unfold AsyncPeriodSleepinessG
  simp only [upAndHonestThroughoutG_observe, mostOfCommitteeG_observe]
  exact Iff.rfl

/-- `HonestProposerThroughG` on a run as observed is `HonestProposerThroughG` on the run. -/
theorem honestProposerThroughG_observe (tAwakeEnd tPreAsync tProposalStart : ℝ) (vProposer : Node) :
    HonestProposerThroughG tAwakeEnd tPreAsync tProposalStart vProposer (observe f x) ↔
      HonestProposerThroughG tAwakeEnd tPreAsync tProposalStart vProposer x := by
  unfold HonestProposerThroughG
  rw [upAndHonestThroughoutG_observe]

end Observe

end Framework.RealStsMulticastMultisetLog

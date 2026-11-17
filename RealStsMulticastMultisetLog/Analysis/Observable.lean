module
public import RealStsMulticastMultisetLog.Spec.Conditions

@[expose] public section

/-!
# The conditions on executions on an observed run with its values read through a function

Theorems about the definitions of `RealStsMulticastMultisetLog.Spec.Observable` and
`RealStsMulticastMultisetLog.Spec.Conditions`, kept out of the specification so that it reads as
definitions only. No condition on executions is assumed, and nothing here is part of the bare
framework.

A run `π` is an observed run (`π.toObservedRun`), so a condition on executions applies to it as it
is, and nothing has to be proved for that. What is proved here is what a condition says on an
observed run `y.map g`, `y` with each node's value `w` replaced by `g w`, and so on a run as
observed, `observe readLocal π`, which is `π.toObservedRun.map readLocal`:

* **The readings.** `y.map g` has `y`'s actions, stamps, clocks, views, sent envelopes, corrupted and
  crashed sets, and a node's value there is the image under `g` of its value in `y`
  (`state_map`); so a node's value is known in `y.map g` exactly when it is known in `y`
  (`state_map_ne_none`). The same readings on `observe readLocal π` are the run's own (`…_observe`).
* **The conditions.** Each condition says on `y.map g` what it says on `y` (`…_map`). A condition
  with a parameter `acting` says so when the two `acting`, one on each observed run, agree; one with
  a parameter `serves` reading a node's value says on `y.map g` what it says on `y` with `serves`
  read through `g`.
* **Under the skew.** `clockAdvancesWithin_bounded`: under `ClockWithinSkew`, `ClockAdvancesWithin`
  gives back the real-time bounds of the change of the clock.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

open ObservedRun

/-! ### The readings of an observed run with its values read through a function -/

section Map

variable {Node Msg V W Lbl : Type} (g : V → W) (y : ObservedRun (ObservedConfig Node Msg V) Lbl)

/-- `y.map g` has `y`'s actions. -/
@[simp] theorem lbl_map (j : Nat) : lbl (y.map g) j = lbl y j := rfl

/-- `y.map g` has `y`'s stamps. -/
@[simp] theorem stamp_map (i : Nat) : stamp (y.map g) i = stamp y i := rfl

/-- `y.map g` has `y`'s clocks. -/
@[simp] theorem clock_map (i : Nat) (p : Node) : clock (y.map g) i p = clock y i p := rfl

/-- In `y.map g` a node's value is the image under `g` of its value in `y`. -/
@[simp] theorem state_map (i : Nat) (p : Node) : state (y.map g) i p = (state y i p).map g := rfl

/-- `y.map g` has `y`'s views. -/
@[simp] theorem view_map (i : Nat) (p : Node) : view (y.map g) i p = view y i p := rfl

/-- `y.map g` has `y`'s sent envelopes. -/
@[simp] theorem sent_map (i : Nat) : sent (y.map g) i = sent y i := rfl

/-- `y.map g` has `y`'s corrupted sets. -/
@[simp] theorem adv_map (i : Nat) : adv (y.map g) i = adv y i := rfl

/-- `y.map g` has `y`'s crashed sets. -/
@[simp] theorem crashed_map (i : Nat) : crashed (y.map g) i = crashed y i := rfl

/-- In `y.map g` a node's value is known exactly when it is known in `y`. -/
theorem state_map_ne_none (i : Nat) (p : Node) : state (y.map g) i p ≠ none ↔ state y i p ≠ none := by
  simp only [state_map, ne_eq, Option.map_eq_none_iff]

/-- `Honest` on `y.map g` is `Honest` on `y`. -/
theorem honest_map (i : Nat) (p : Node) : (y.map g).Honest i p ↔ y.Honest i p := Iff.rfl

/-- `InForce` on `y.map g` is `InForce` on `y`. -/
theorem inForce_map (i : Nat) (s : ℝ) : (y.map g).InForce i s ↔ y.InForce i s := Iff.rfl

end Map

/-! ### The readings of a run as observed -/

section Observe

variable {Node Msg NodeState Ev V : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (readLocal : Local Node Msg NodeState → V) (π : Exec Pr)

/-- A run as observed is the run's observed run with each local state read through `readLocal`. -/
theorem observe_eq_map : observe readLocal π = π.toObservedRun.map readLocal := rfl

/-- A run as observed has the run's actions. -/
@[simp] theorem lbl_observe (j : Nat) : lbl (observe readLocal π) j = π.lbl j := rfl

/-- A run as observed has the run's stamps. -/
@[simp] theorem stamp_observe (i : Nat) : stamp (observe readLocal π) i = π.stamp i := rfl

/-- A run as observed has the run's clocks. -/
@[simp] theorem clock_observe (i : Nat) (p : Node) :
    clock (observe readLocal π) i p = π[i].clock p := rfl

/-- On a run as observed, a node's value is what `readLocal` reads of its local state on the run. -/
@[simp] theorem state_observe (i : Nat) (p : Node) :
    state (observe readLocal π) i p = (π[i][p]).map readLocal := rfl

/-- A run as observed has the run's views. -/
@[simp] theorem view_observe (i : Nat) (p : Node) : view (observe readLocal π) i p = π[i].view p :=
  rfl

/-- A run as observed has the run's sent envelopes. -/
@[simp] theorem sent_observe (i : Nat) : sent (observe readLocal π) i = π[i].sent := rfl

/-- A run as observed has the run's corrupted sets. -/
@[simp] theorem adv_observe (i : Nat) : adv (observe readLocal π) i = π[i].adv := rfl

/-- A run as observed has the run's crashed sets. -/
@[simp] theorem crashed_observe (i : Nat) : crashed (observe readLocal π) i = π[i].crashed := rfl

end Observe

/-! ### The conditions on an observed run with its values read through a function -/

section Conditions

variable {Node Msg V W Ev : Type} [DecidableEq Node] [DecidableEq Msg] (g : V → W)
  (y : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev))

/-- `NoCrashDuring` on `y.map g` is `NoCrashDuring` on `y`. -/
theorem noCrashDuring_map : NoCrashDuring (y.map g) ↔ NoCrashDuring y := Iff.rfl

/-- `ClockWithinSkew` on `y.map g` is `ClockWithinSkew` on `y`. -/
theorem clockWithinSkew_map (ΔClockAhead ΔClockBehind : ℝ) :
    ClockWithinSkew ΔClockAhead ΔClockBehind (y.map g) ↔ ClockWithinSkew ΔClockAhead ΔClockBehind y :=
  Iff.rfl

/-- `ClockAdvancesWithin` on `y.map g` is `ClockAdvancesWithin` on `y`. -/
theorem clockAdvancesWithin_map (ΔClockAhead ΔClockBehind : ℝ) :
    ClockAdvancesWithin ΔClockAhead ΔClockBehind (y.map g) ↔
      ClockAdvancesWithin ΔClockAhead ΔClockBehind y := by
  unfold ClockAdvancesWithin
  simp only [state_map_ne_none]
  exact Iff.rfl

/-- `TicksWithin` on `y.map g` is `TicksWithin` on `y`. -/
theorem ticksWithin_map (ΔClockBehind : ℝ) : TicksWithin ΔClockBehind (y.map g) ↔ TicksWithin ΔClockBehind y := by
  unfold TicksWithin
  simp only [state_map_ne_none]
  exact Iff.rfl

/-- `ActsWithinSkew` on `y.map g` is `ActsWithinSkew` on `y`. -/
theorem actsWithinSkew_map (ΔClockBehind : ℝ) :
    ActsWithinSkew ΔClockBehind (y.map g) ↔ ActsWithinSkew ΔClockBehind y :=
  Iff.rfl

/-- `DiligentWithin` on `y.map g` is `DiligentWithin` on `y`. -/
theorem diligentWithin_map (ΔClockAhead ΔClockBehind : ℝ) :
    DiligentWithin ΔClockAhead ΔClockBehind (y.map g) ↔ DiligentWithin ΔClockAhead ΔClockBehind y :=
  and_congr (clockAdvancesWithin_map g y _ _) (ticksWithin_map g y _)

/-- `ActingStep` on `y.map g` is `ActingStep` on `y`. -/
theorem actingStep_map (k : Nat) (p : Node) : ActingStep (y.map g) k p ↔ ActingStep y k p := Iff.rfl

/-- `TickStep` on `y.map g` is `TickStep` on `y`. -/
theorem tickStep_map (k : Nat) (p : Node) : TickStep (y.map g) k p ↔ TickStep y k p := Iff.rfl

/-- `UpBetween` on `y.map g` is `UpBetween` on `y`. -/
theorem upBetween_map (i k : Nat) (p : Node) : UpBetween (y.map g) i k p ↔ UpBetween y i k p := by
  unfold UpBetween
  simp only [state_map_ne_none]
  exact Iff.rfl

/-- `UpAndHonestThroughout` on `y.map g` is `UpAndHonestThroughout` on `y`. -/
theorem upAndHonestThroughout_map (t t' : ℝ) (p : Node) :
    UpAndHonestThroughout (y.map g) t t' p ↔ UpAndHonestThroughout y t t' p := by
  unfold UpAndHonestThroughout
  simp only [state_map_ne_none]
  exact Iff.rfl

/-- `UpAndHonestUntilActing` on `y.map g` is `UpAndHonestUntilActing` on `y`, when the acting steps
    read on `y.map g` (`actingW`) are those read on `y` (`actingV`). -/
theorem upAndHonestUntilActing_map
    (actingW : ObservedRun (ObservedConfig Node Msg W) (Action Node Msg Ev) → Nat → Node → Prop)
    (actingV : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev) → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingW (y.map g) k p ↔ actingV y k p) (t t' : ℝ) (p : Node) :
    UpAndHonestUntilActing actingW (y.map g) t t' p ↔ UpAndHonestUntilActing actingV y t t' p := by
  unfold UpAndHonestUntilActing
  simp only [hacting, state_map_ne_none]
  exact Iff.rfl

/-- `DueBy` on `y.map g` is `DueBy` on `y`. -/
theorem dueBy_map (dl : (m : Msg) → (tSend : ℝ) → ℝ) (i : Nat) (e : Envelope Node Msg) (t : ℝ) :
    DueBy dl (y.map g) i e t ↔ DueBy dl y i e t :=
  Iff.rfl

/-- `NetworkSynchrony` on `y.map g` is `NetworkSynchrony` on `y`, when the acting steps
    read on `y.map g` (`actingW`) are those read on `y` (`actingV`). -/
theorem networkSynchrony_map
    (actingW : ObservedRun (ObservedConfig Node Msg W) (Action Node Msg Ev) → Nat → Node → Prop)
    (actingV : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev) → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingW (y.map g) k p ↔ actingV y k p)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) :
    NetworkSynchrony actingW dl (y.map g) ↔ NetworkSynchrony actingV dl y := by
  unfold NetworkSynchrony
  simp only [hacting, upBetween_map]
  exact Iff.rfl

/-- `CatchUpAfterRestart` on `y.map g` is `CatchUpAfterRestart` on `y`, when the acting steps read on
    `y.map g` (`actingW`) are those read on `y` (`actingV`). -/
theorem catchUpAfterRestart_map
    (actingW : ObservedRun (ObservedConfig Node Msg W) (Action Node Msg Ev) → Nat → Node → Prop)
    (actingV : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev) → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingW (y.map g) k p ↔ actingV y k p)
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) (dlW : (m : Msg) → (tRestart : ℝ) → ℝ) :
    CatchUpAfterRestart actingW dl dlW (y.map g) ↔ CatchUpAfterRestart actingV dl dlW y := by
  unfold CatchUpAfterRestart
  simp only [hacting]
  exact Iff.rfl

/-- `SyncedWithinBy` on `y.map g`, with `serves` reading a node's value of type `W`, is
    `SyncedWithinBy` on `y` with `serves` read through `g`, when the acting steps read on `y.map g`
    (`actingW`) are those read on `y` (`actingV`). -/
theorem syncedWithinBy_map
    (actingW : ObservedRun (ObservedConfig Node Msg W) (Action Node Msg Ev) → Nat → Node → Prop)
    (actingV : ObservedRun (ObservedConfig Node Msg V) (Action Node Msg Ev) → Nat → Node → Prop)
    (hacting : ∀ (k : Nat) (p : Node), actingW (y.map g) k p ↔ actingV y k p)
    (serves : (tClock : Time) → (w : W) → (m : Msg) → Prop) (sync : (m : Msg) → (t : ℝ) → ℝ) :
    SyncedWithinBy actingW serves sync (y.map g) ↔
      SyncedWithinBy actingV (fun tClock v m => serves tClock (g v) m) sync y := by
  unfold SyncedWithinBy
  simp only [upAndHonestUntilActing_map g y actingW actingV hacting, hacting, state_map,
    Option.map_eq_some_iff, ne_eq, Option.map_eq_none_iff]
  constructor
  · intro h t i p p' m tClock v hin hcr hh hv hclk hserv hup
    rcases h t i p p' m tClock (g v) hin hcr hh ⟨v, hv, rfl⟩ hclk hserv hup with
      ⟨tClock'', _, ⟨v'', hv'', rfl⟩, hclk'', hserv''⟩ |
      ⟨j, i', e, tClock', _, hij, hst, ⟨v', hv', rfl⟩, hclk', hserv', hrest⟩
    · exact Or.inl ⟨tClock'', v'', hv'', hclk'', hserv''⟩
    · exact Or.inr ⟨j, i', e, tClock', v', hij, hst, hv', hclk', hserv', hrest⟩
  · rintro h t i p p' m tClock _ hin hcr hh ⟨v, hv, rfl⟩ hclk hserv hup
    rcases h t i p p' m tClock v hin hcr hh hv hclk hserv hup with
      ⟨tClock'', v'', hv'', hclk'', hserv''⟩ |
      ⟨j, i', e, tClock', v', hij, hst, hv', hclk', hserv', hrest⟩
    · exact Or.inl ⟨tClock'', g v'', ⟨v'', hv'', rfl⟩, hclk'', hserv''⟩
    · exact Or.inr ⟨j, i', e, tClock', g v', hij, hst, ⟨v', hv', rfl⟩, hclk', hserv', hrest⟩

/-- `TickOncePerReading` on `y.map g` is `TickOncePerReading` on `y`. -/
theorem tickOncePerReading_map : TickOncePerReading (y.map g) ↔ TickOncePerReading y := Iff.rfl

/-- `UnforgeableSends` on `y.map g` is `UnforgeableSends` on `y`. -/
theorem unforgeableSends_map (author : (m : Msg) → Option Node) (carries : (m : Msg) → (m' : Msg) → Prop) :
    UnforgeableSends author carries (y.map g) ↔ UnforgeableSends author carries y :=
  Iff.rfl

end Conditions

/-! ### Under the skew -/

/-- Under `ClockWithinSkew`, `ClockAdvancesWithin` gives back the case with the real-time bounds:
    the step that sets the clock to `t` is at a real time in `[t − ΔClockAhead, t + ΔClockBehind]`.
    Both are conditions on executions, which no step of the bare framework reads.

    Read aloud: if every step `setClock p t` is at a real time in `[t − ΔClockAhead,
    t + ΔClockBehind]`, and the clock condition `ClockAdvancesWithin` holds, then whenever a node
    `p` is up, not corrupted, and its clock reads less than a reading `t`, either some step `j` sets
    `p`'s clock to `t` at a real time `stamp x (j + 1)` in that interval, or `p` crashes or is
    corrupted after configuration `i`, by the real time `t + ΔClockBehind`. -/
theorem clockAdvancesWithin_bounded {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {ΔClockAhead ΔClockBehind : ℝ} {x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)}
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

end Framework.RealStsMulticastMultisetLog

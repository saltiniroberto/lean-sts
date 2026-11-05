module
public import RealStsMulticastMultisetLog.Spec.Protocol

@[expose] public section

/-!
# What the bare framework's helpers and reactions do

Theorems about the helpers of the bare framework `RealStsMulticastMultisetLog`
(`RealStsMulticastMultisetLog.Spec.Protocol`), kept out of the specification so that it reads as
definitions only; `RealStsMulticastMultisetLog.Analysis.Lemmas` imports this page and goes on to the
steps and the executions.

* **Read-backs.** For each helper (`Config.setNode`, `receive`, `setClock`, `applyEffect`,
  `applyEffects`, `applyNodeStepResult`, `applyCrashDuring`, `NodeAction.prepare`): what each
  field of the configuration is afterwards. A local state `c[v]` is an `Option`; the writes to a
  part of it change nothing when it is unknown, so the read-backs say what happens in both cases.
* **Reactions.** What a completed reaction (`NodeStep`) and an interrupted one (`CrashDuringStep`)
  may change.

The read-backs that return an `if` (`receive_view`, `setClock_clock`) are cited explicitly, not
`simp`; `Config.setNode_apply` is a `simp` lemma.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-! ### Read-backs of the helpers -/

/-! #### `Config.setNode` -/

/-- After `c.setNode v r`, `v`'s local state is `r` and every other validator's is `c`'s (the bare
    framework). -/
@[simp] theorem Config.setNode_apply {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) (v' : Node) :
    (c.setNode v r)[v'] = if v = v' then r else c[v'] := rfl

/-- After `c.setNode v r`, `v`'s local state is `r` (the bare framework). -/
theorem Config.setNode_self {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r)[v] = r := by
  simp

/-- After `c.setNode v r`, every validator other than `v` has `c`'s local state (the bare
    framework). -/
theorem Config.setNode_other {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (c.setNode v r)[v'] = c[v'] := by
  simp [Ne.symm h]

/-- `Config.setNode` changes no clock (the bare framework). -/
@[simp] theorem Config.setNode_clock {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r).clock = c.clock := rfl

/-- `Config.setNode` changes no view (the bare framework). -/
@[simp] theorem Config.setNode_view {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r).view = c.view := rfl

/-- `Config.setNode` changes no sent log (the bare framework). -/
@[simp] theorem Config.setNode_sent {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r).sent = c.sent := rfl

/-- `Config.setNode` changes no corrupted set (the bare framework). -/
@[simp] theorem Config.setNode_adv {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r).adv = c.adv := rfl

/-- `Config.setNode` changes no crashed set (the bare framework). -/
@[simp] theorem Config.setNode_crashed {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    (c.setNode v r).crashed = c.crashed := rfl

/-! #### `receive` -/

/-- `receive` changes no local state: the view is not part of it (the bare framework). -/
@[simp] theorem receive_getElem {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v v' : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c)[v'] = c[v'] := rfl

set_option linter.unusedVariables false in
/-- `receive v m` leaves every validator's local state as it was, another validator's in
    particular (the bare framework). -/
theorem receive_getElem_other {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v v' : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (receive v m c)[v'] = c[v'] := rfl

/-- `receive` changes no clock (the bare framework). -/
@[simp] theorem receive_clock {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).clock = c.clock := rfl

/-- After `receive v m c`, `v`'s view has `m` filed into it, and every other view is `c`'s (the
    bare framework). -/
theorem receive_view {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v v' : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).view v' = if v = v' then insert m (c.view v) else c.view v' := rfl

/-- After `receive v m c`, `v`'s view is `c`'s with `m` filed into it (the bare framework). -/
@[simp] theorem receive_view_self {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).view v = insert m (c.view v) := by
  simp [receive_view]

/-- `receive v m` leaves every other validator's view as it was (the bare framework). -/
theorem receive_view_other {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v v' : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (receive v m c).view v' = c.view v' := by
  simp [receive_view, Ne.symm h]

/-- `receive` changes no sent log (the bare framework). -/
@[simp] theorem receive_sent {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).sent = c.sent := rfl

/-- `receive` changes no corrupted set (the bare framework). -/
@[simp] theorem receive_adv {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).adv = c.adv := rfl

/-- `receive` changes no crashed set (the bare framework). -/
@[simp] theorem receive_crashed {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node) (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) :
    (receive v m c).crashed = c.crashed := rfl

/-! #### `setClock` -/

/-- `setClock` changes no local state: the clock is not part of it (the bare framework). -/
@[simp] theorem setClock_getElem {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (t : Time) (c : Config Node Msg NodeState) : (setClock v t c)[v'] = c[v'] := rfl

set_option linter.unusedVariables false in
/-- `setClock v t` leaves every validator's local state as it was, another validator's in
    particular (the bare framework). -/
theorem setClock_getElem_other {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (t : Time) (c : Config Node Msg NodeState) (h : v' ≠ v) : (setClock v t c)[v'] = c[v'] := rfl

/-- After `setClock v t c`, `v`'s clock reads `t`, and every other clock is `c`'s (the bare
    framework). -/
theorem setClock_clock {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node) (t : Time)
    (c : Config Node Msg NodeState) :
    (setClock v t c).clock v' = if v = v' then some t else c.clock v' := rfl

/-- After `setClock v t c`, `v`'s clock reads `t` (the bare framework). -/
@[simp] theorem setClock_clock_self {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (t : Time) (c : Config Node Msg NodeState) : (setClock v t c).clock v = some t := by
  simp [setClock_clock]

/-- `setClock v t` leaves every other validator's clock as it was (the bare framework). -/
theorem setClock_clock_other {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (t : Time) (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (setClock v t c).clock v' = c.clock v' := by
  simp [setClock_clock, Ne.symm h]

/-- `setClock` changes no view (the bare framework). -/
@[simp] theorem setClock_view {Node Msg NodeState : Type} [DecidableEq Node] (v : Node) (t : Time)
    (c : Config Node Msg NodeState) : (setClock v t c).view = c.view := rfl

/-- `setClock` changes no sent log (the bare framework). -/
@[simp] theorem setClock_sent {Node Msg NodeState : Type} [DecidableEq Node] (v : Node) (t : Time)
    (c : Config Node Msg NodeState) : (setClock v t c).sent = c.sent := rfl

/-- `setClock` changes no corrupted set (the bare framework). -/
@[simp] theorem setClock_adv {Node Msg NodeState : Type} [DecidableEq Node] (v : Node) (t : Time)
    (c : Config Node Msg NodeState) : (setClock v t c).adv = c.adv := rfl

/-- `setClock` changes no crashed set (the bare framework). -/
@[simp] theorem setClock_crashed {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (t : Time) (c : Config Node Msg NodeState) : (setClock v t c).crashed = c.crashed := rfl

/-! #### `applyEffect` and `applyEffects` -/

/-- A send puts the addressed message on the wire, signed by `v` (the bare framework). -/
theorem applyEffect_send {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (a : Addressed Node Msg) :
    applyEffect v (.send a) c = { c with sent := a.sign v ::ₘ c.sent } := rfl

/-- A write sets `v`'s disk when `v`'s local state is known, and changes nothing when it is
    unknown (the bare framework). -/
theorem applyEffect_write {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (s : NodeState) :
    applyEffect v (.write s) c = c.setNode v (c[v].map fun l => { l with disk := s }) := rfl

/-- A write of `s` leaves `s` on `v`'s disk when `v`'s local state is known, and leaves it unknown
    otherwise (the bare framework). -/
@[simp] theorem applyEffect_write_getElem_self {Node Msg NodeState : Type} [DecidableEq Node]
    (v : Node) (c : Config Node Msg NodeState) (s : NodeState) :
    (applyEffect v (.write s) c)[v] = c[v].map fun l => { l with disk := s } := by
  simp [applyEffect]

/-- A send changes no local state (the bare framework). -/
@[simp] theorem applyEffect_send_getElem {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (c : Config Node Msg NodeState) (a : Addressed Node Msg) :
    (applyEffect v (.send a) c)[v'] = c[v'] := rfl

/-- An effect changes no corrupted set (the bare framework). -/
@[simp] theorem applyEffect_adv {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) :
    (applyEffect v ef c).adv = c.adv := by
  cases ef <;> rfl

/-- An effect changes no crashed set (the bare framework). -/
@[simp] theorem applyEffect_crashed {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) :
    (applyEffect v ef c).crashed = c.crashed := by
  cases ef <;> rfl

/-- An effect changes no clock (the bare framework). -/
@[simp] theorem applyEffect_clock {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) :
    (applyEffect v ef c).clock = c.clock := by
  cases ef <;> rfl

/-- An effect changes no view (the bare framework). -/
@[simp] theorem applyEffect_view {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) :
    (applyEffect v ef c).view = c.view := by
  cases ef <;> rfl

/-- An effect of `v` leaves every other validator's local state alone (the bare framework). -/
theorem applyEffect_getElem_other {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) (h : v' ≠ v) :
    (applyEffect v ef c)[v'] = c[v'] := by
  cases ef with
  | send a => rfl
  | write s => simp [applyEffect, Ne.symm h]

/-- An effect keeps a known local state known, with the same memory: only the disk may change (the
    bare framework). -/
theorem applyEffect_getElem_of_some {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState)
    {l : Local Node Msg NodeState} (hl : c[v'] = some l) :
    ∃ d : NodeState, (applyEffect v ef c)[v'] = some { l with disk := d } := by
  cases ef with
  | send a => exact ⟨l.disk, hl⟩
  | write s =>
      by_cases hv : v = v'
      · subst hv; exact ⟨s, by simp [applyEffect, hl]⟩
      · exact ⟨l.disk, by rw [applyEffect_getElem_other v v' c _ (Ne.symm hv)]; exact hl⟩

/-- An effect keeps an unknown local state unknown, and a known one known (the bare framework). -/
theorem applyEffect_getElem_eq_none_iff {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState) :
    (applyEffect v ef c)[v'] = none ↔ c[v'] = none := by
  cases ef with
  | send a => rfl
  | write s =>
      by_cases hv : v = v'
      · subst hv; simp [applyEffect]
      · rw [applyEffect_getElem_other v v' c _ (Ne.symm hv)]

/-- No effect applied (the bare framework). -/
theorem applyEffects_nil {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) : applyEffects v [] c = c := rfl

/-- The effects `ef :: effs` are `ef`, then `effs` (the bare framework). -/
theorem applyEffects_cons {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (ef : NodeEffect Node Msg NodeState)
    (effs : List (NodeEffect Node Msg NodeState)) :
    applyEffects v (ef :: effs) c = applyEffects v effs (applyEffect v ef c) := rfl

/-- Effects change no corrupted set (the bare framework). -/
@[simp] theorem applyEffects_adv {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c).adv = c.adv := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_adv]

/-- Effects change no crashed set (the bare framework). -/
@[simp] theorem applyEffects_crashed {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c).crashed = c.crashed := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_crashed]

/-- Effects change no clock (the bare framework). -/
@[simp] theorem applyEffects_clock {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c).clock = c.clock := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_clock]

/-- Effects change no view (the bare framework). -/
@[simp] theorem applyEffects_view {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c).view = c.view := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_view]

/-- The effects of `v` leave every other validator's local state alone (the bare framework). -/
theorem applyEffects_getElem_other {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) (h : v' ≠ v) :
    (applyEffects v effs c)[v'] = c[v'] := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_getElem_other v v' c ef h]

/-- Effects keep a known local state known, with the same memory: only the disk may change (the
    bare framework). -/
theorem applyEffects_getElem_of_some {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState))
    {l : Local Node Msg NodeState} (hl : c[v'] = some l) :
    ∃ d : NodeState, (applyEffects v effs c)[v'] = some { l with disk := d } := by
  induction effs generalizing c l with
  | nil => exact ⟨l.disk, hl⟩
  | cons ef effs ih =>
      obtain ⟨d₁, h₁⟩ := applyEffect_getElem_of_some v v' c ef hl
      obtain ⟨d, h⟩ := ih (applyEffect v ef c) h₁
      exact ⟨d, by rw [applyEffects_cons]; exact h⟩

/-- Effects keep an unknown local state unknown, and a known one known (the bare framework). -/
theorem applyEffects_getElem_eq_none_iff {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c)[v'] = none ↔ c[v'] = none := by
  induction effs generalizing c with
  | nil => rfl
  | cons ef effs ih => rw [applyEffects_cons, ih, applyEffect_getElem_eq_none_iff]

/-- Effects change no memory: the memory a local state holds, when known, is `c`'s (the bare
    framework). -/
theorem applyEffects_st {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c)[v'].map Local.st = c[v'].map Local.st := by
  cases hl : c[v'] with
  | none => rw [(applyEffects_getElem_eq_none_iff v v' c effs).2 hl]
  | some l =>
      obtain ⟨d, h⟩ := applyEffects_getElem_of_some v v' c effs hl
      rw [h]; rfl

/-- The effects of `v` add to the sent log exactly their sends, each signed by `v`; the writes add
    nothing (the bare framework). -/
theorem applyEffects_sent {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    (applyEffects v effs c).sent =
      c.sent + ((effs.filterMap fun ef => match ef with
        | .send a => some (a.sign v)
        | .write _ => none : List (Envelope Node Msg)) : Multiset (Envelope Node Msg)) := by
  induction effs generalizing c with
  | nil => simp [applyEffects_nil]
  | cons ef effs ih =>
      rw [applyEffects_cons, ih]
      cases ef with
      | send a =>
          simp only [applyEffect_send, List.filterMap_cons, Multiset.cons_add]
          rw [← Multiset.cons_coe, Multiset.add_cons]
      | write s => simp [applyEffect_write, Config.setNode]

/-- Effects only add to the sent log (the bare framework). -/
theorem applyEffects_sent_le {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState)) :
    c.sent ≤ (applyEffects v effs c).sent := by
  rw [applyEffects_sent]; exact Multiset.le_add_right _ _

/-- An envelope the effects of `v` added to the sent log is signed by `v`, and is the signed form
    of one of the effects' sends (the bare framework). -/
theorem mem_applyEffects_sent_sub {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg]
    (v : Node)
    (c : Config Node Msg NodeState) (effs : List (NodeEffect Node Msg NodeState))
    {e : Envelope Node Msg} (he : e ∈ (applyEffects v effs c).sent - c.sent) :
    e.sender = v ∧ NodeEffect.send { msg := e.msg, recipients := e.recipients } ∈ effs := by
  rw [applyEffects_sent, add_tsub_cancel_left] at he
  obtain ⟨ef, hef, hsome⟩ := List.mem_filterMap.1 (Multiset.mem_coe.1 he)
  cases ef with
  | send a =>
      obtain rfl : a.sign v = e := Option.some_injective _ hsome
      exact ⟨rfl, hef⟩
  | write s => exact absurd hsome (by simp)

/-! #### `applyNodeStepResult`: a completed reaction -/

/-- After a completed reaction of `v`, `v`'s local state, when known, holds the reaction's new
    memory state and, on its disk, `Pr.persist` of it; an unknown local state stays unknown (the
    bare framework). -/
theorem applyNodeStepResult_getElem_self {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) :
    (applyNodeStepResult Pr v res c)[v] =
      c[v].map fun l => { l with st := res.state, disk := Pr.persist res.state } := by
  show ((applyEffects v res.effects c).setNode v _)[v] = _
  rw [Config.setNode_self]
  cases hl : c[v] with
  | none => rw [(applyEffects_getElem_eq_none_iff v v c res.effects).2 hl]
  | some l =>
      obtain ⟨d, h⟩ := applyEffects_getElem_of_some v v c res.effects hl
      rw [h]; rfl

/-- After a completed reaction of `v` from a known local state `l`, `v`'s local state is `l` with
    the reaction's new memory state and, on its disk, `Pr.persist` of it (the bare framework). -/
theorem applyNodeStepResult_getElem_self_of_some {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) {l : Local Node Msg NodeState} (hl : c[v] = some l) :
    (applyNodeStepResult Pr v res c)[v] =
      some { l with st := res.state, disk := Pr.persist res.state } := by
  rw [applyNodeStepResult_getElem_self, hl]; rfl

/-- A completed reaction of `v` leaves every other validator's local state alone (the bare
    framework). -/
theorem applyNodeStepResult_getElem_other {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v v' : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (applyNodeStepResult Pr v res c)[v'] = c[v'] := by
  show ((applyEffects v res.effects c).setNode v _)[v'] = _
  rw [Config.setNode_other v v' _ _ h, applyEffects_getElem_other v v' c _ h]

/-- A completed reaction keeps an unknown local state unknown, and a known one known (the bare
    framework). -/
theorem applyNodeStepResult_getElem_eq_none_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v v' : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) :
    (applyNodeStepResult Pr v res c)[v'] = none ↔ c[v'] = none := by
  by_cases hv : v' = v
  · subst hv; rw [applyNodeStepResult_getElem_self]; simp
  · rw [applyNodeStepResult_getElem_other Pr v v' res c hv]

/-- A completed reaction changes no corrupted set (the bare framework). -/
@[simp] theorem applyNodeStepResult_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) : (applyNodeStepResult Pr v res c).adv = c.adv :=
  applyEffects_adv v c res.effects

/-- A completed reaction changes no crashed set (the bare framework). -/
@[simp] theorem applyNodeStepResult_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) : (applyNodeStepResult Pr v res c).crashed = c.crashed :=
  applyEffects_crashed v c res.effects

/-- A completed reaction changes no clock (the bare framework). -/
@[simp] theorem applyNodeStepResult_clock {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) : (applyNodeStepResult Pr v res c).clock = c.clock :=
  applyEffects_clock v c res.effects

/-- A completed reaction changes no view (the bare framework). -/
@[simp] theorem applyNodeStepResult_view {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) : (applyNodeStepResult Pr v res c).view = c.view :=
  applyEffects_view v c res.effects

/-- A completed reaction's sent log is the one its effects leave (the bare framework). -/
theorem applyNodeStepResult_sent {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (v : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) :
    (applyNodeStepResult Pr v res c).sent = (applyEffects v res.effects c).sent := rfl

/-! #### `applyCrashDuring`: an interrupted reaction -/

/-- After a reaction of `v` interrupted after `k` effects, every local state is the one the first
    `k` effects leave: no new memory state, no final write (the bare framework). -/
theorem applyCrashDuring_getElem {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c)[v'] = (applyEffects v (res.effects.take k) c)[v'] := rfl

/-- An interrupted reaction changes no corrupted set (the bare framework). -/
@[simp] theorem applyCrashDuring_adv {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c).adv = c.adv :=
  applyEffects_adv v c _

/-- An interrupted reaction puts its validator into `crashed` (the bare framework). -/
@[simp] theorem applyCrashDuring_crashed {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c).crashed = insert v c.crashed := by
  show insert v (applyEffects v (res.effects.take k) c).crashed = _
  rw [applyEffects_crashed]

/-- An interrupted reaction's sent log is the one its first `k` effects leave (the bare
    framework). -/
theorem applyCrashDuring_sent {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c).sent = (applyEffects v (res.effects.take k) c).sent := rfl

/-- An interrupted reaction changes no clock (the bare framework). -/
@[simp] theorem applyCrashDuring_clock {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c).clock = c.clock :=
  applyEffects_clock v c _

/-- An interrupted reaction changes no view (the bare framework). -/
@[simp] theorem applyCrashDuring_view {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c).view = c.view :=
  applyEffects_view v c _

/-- An interrupted reaction discards the new memory state: the memory a local state holds, when
    known, is `c`'s (the bare framework). -/
theorem applyCrashDuring_st {Node Msg NodeState : Type} [DecidableEq Node] (v v' : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c)[v'].map Local.st = c[v'].map Local.st := by
  rw [applyCrashDuring_getElem, applyEffects_st]

/-- An interrupted reaction keeps a known local state known, with the same memory: only the disk
    may change (the bare framework). -/
theorem applyCrashDuring_getElem_of_some {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (res : NodeStepResult Node NodeState Msg) (k : Nat)
    (c : Config Node Msg NodeState) {l : Local Node Msg NodeState} (hl : c[v'] = some l) :
    ∃ d : NodeState, (applyCrashDuring v res k c)[v'] = some { l with disk := d } := by
  rw [applyCrashDuring_getElem]; exact applyEffects_getElem_of_some v v' c _ hl

/-- An interrupted reaction keeps an unknown local state unknown, and a known one known (the bare
    framework). -/
theorem applyCrashDuring_getElem_eq_none_iff {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (res : NodeStepResult Node NodeState Msg) (k : Nat)
    (c : Config Node Msg NodeState) :
    (applyCrashDuring v res k c)[v'] = none ↔ c[v'] = none := by
  rw [applyCrashDuring_getElem, applyEffects_getElem_eq_none_iff]

/-- An interrupted reaction of `v` leaves every other validator's local state alone (the bare
    framework). -/
theorem applyCrashDuring_getElem_other {Node Msg NodeState : Type} [DecidableEq Node]
    (v v' : Node) (res : NodeStepResult Node NodeState Msg) (k : Nat)
    (c : Config Node Msg NodeState) (h : v' ≠ v) :
    (applyCrashDuring v res k c)[v'] = c[v'] := by
  rw [applyCrashDuring_getElem, applyEffects_getElem_other v v' c _ h]

/-- A reaction interrupted after `k` effects, `k` at or past the length of its list of effects,
    applies every effect: the configuration is the one all the effects leave, with `v` put into
    `crashed`; the final write is still skipped and the new memory state still discarded (the bare
    framework). -/
theorem applyCrashDuring_of_length_le {Node Msg NodeState : Type} [DecidableEq Node] (v : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState)
    (hk : res.effects.length ≤ k) :
    applyCrashDuring v res k c =
      { applyEffects v res.effects c with crashed := insert v c.crashed } := by
  simp only [applyCrashDuring, List.take_of_length_le hk, applyEffects_crashed]

/-! #### `NodeAction.prepare` -/

/-- A tick's reaction starts from the configuration itself (the bare framework). -/
@[simp] theorem NodeAction.prepare_tick {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (c : Config Node Msg NodeState) :
    (NodeAction.tick : NodeAction Node Msg Ev).prepare v c = c := rfl

/-- A delivery's reaction starts from the configuration with the delivered message filed into the
    recipient's view (the bare framework). -/
@[simp] theorem NodeAction.prepare_deliver {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (e : Envelope Node Msg) (c : Config Node Msg NodeState) :
    (NodeAction.deliver e : NodeAction Node Msg Ev).prepare v c = receive v e.toSignedMsg c := rfl

/-- A protocol event's reaction starts from the configuration itself (the bare framework). -/
@[simp] theorem NodeAction.prepare_custom {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (ev : Ev) (c : Config Node Msg NodeState) :
    (NodeAction.custom ev : NodeAction Node Msg Ev).prepare v c = c := rfl

/-- Preparing a node action changes no local state (the bare framework). -/
@[simp] theorem NodeAction.prepare_getElem {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v v' : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev) :
    (na.prepare v c)[v'] = c[v'] := by
  cases na <;> rfl

set_option linter.unusedVariables false in
/-- Preparing a node action of `v` leaves every validator's local state alone, another validator's
    in particular (the bare framework). -/
theorem NodeAction.prepare_getElem_other {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v v' : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev)
    (h : v' ≠ v) : (na.prepare v c)[v'] = c[v'] :=
  NodeAction.prepare_getElem v v' c na

/-- Preparing a node action changes no clock (the bare framework). -/
@[simp] theorem NodeAction.prepare_clock {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev) :
    (na.prepare v c).clock = c.clock := by
  cases na <;> rfl

/-- Preparing a node action changes no corrupted set (the bare framework). -/
@[simp] theorem NodeAction.prepare_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev) :
    (na.prepare v c).adv = c.adv := by
  cases na <;> rfl

/-- Preparing a node action changes no crashed set (the bare framework). -/
@[simp] theorem NodeAction.prepare_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev) :
    (na.prepare v c).crashed = c.crashed := by
  cases na <;> rfl

/-- Preparing a node action changes no sent log (the bare framework). -/
@[simp] theorem NodeAction.prepare_sent {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev) :
    (na.prepare v c).sent = c.sent := by
  cases na <;> rfl

/-- Preparing a node action of `v` leaves every other validator's view alone (the bare
    framework). -/
theorem NodeAction.prepare_view_other {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] (v v' : Node) (c : Config Node Msg NodeState) (na : NodeAction Node Msg Ev)
    (h : v' ≠ v) : (na.prepare v c).view v' = c.view v' := by
  cases na with
  | tick => rfl
  | deliver e => exact receive_view_other v v' _ c h
  | custom ev => rfl

/-! ### What a reaction may change -/

/-- A completed reaction changes no corrupted set (the bare framework). -/
theorem NodeStep.adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') : c'.adv = pre.adv := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- A completed reaction changes no crashed set (the bare framework). -/
theorem NodeStep.crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') :
    c'.crashed = pre.crashed := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- A completed reaction of `v` leaves every other validator's local state alone (the bare
    framework). -/
theorem NodeStep.other {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') (v' : Node) (hv : v' ≠ v) :
    c'[v'] = pre[v'] := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; exact applyNodeStepResult_getElem_other Pr v v' res pre hv

/-- A completed reaction changes no clock (the bare framework). -/
theorem NodeStep.clock {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') : c'.clock = pre.clock := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- A completed reaction changes no view (the bare framework). -/
theorem NodeStep.view {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') : c'.view = pre.view := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- A completed reaction of `v` runs from a known local state `l` and leaves `v`'s local state
    known, as `l` with the reaction's new memory state and, on its disk, `Pr.persist` of it (the
    bare framework). -/
theorem NodeStep.getElem_self {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') :
    ∃ (l : Local Node Msg NodeState) (s : NodeState),
      pre[v] = some l ∧ c'[v] = some { l with st := s, disk := Pr.persist s } := by
  obtain ⟨l, -, res, hl, -, -, rfl⟩ := h
  exact ⟨l, res.state, hl, applyNodeStepResult_getElem_self_of_some Pr v res pre hl⟩

/-- After a completed reaction of `v`, `v`'s local state is known, and its disk is `Pr.persist` of
    its memory (the bare framework). -/
theorem NodeStep.disk {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') :
    ∃ l : Local Node Msg NodeState, c'[v] = some l ∧ l.disk = Pr.persist l.st := by
  obtain ⟨l, s, -, h'⟩ := h.getElem_self
  exact ⟨_, h', rfl⟩

/-- A completed reaction keeps an unknown local state unknown, and a known one known (the bare
    framework). -/
theorem NodeStep.getElem_eq_none_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') (v' : Node) :
    c'[v'] = none ↔ pre[v'] = none := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; exact applyNodeStepResult_getElem_eq_none_iff Pr v v' res pre

/-- A completed reaction only adds to the sent log (the bare framework). -/
theorem NodeStep.sent_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') : pre.sent ≤ c'.sent := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h
  rw [applyNodeStepResult_sent]; exact applyEffects_sent_le v pre _

/-- Every envelope a completed reaction of `v` adds to the sent log is signed by `v` (the bare
    framework). -/
theorem NodeStep.sent_signed {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev}
    {pre c' : Config Node Msg NodeState} (h : NodeStep Pr v e pre c') (env : Envelope Node Msg)
    (henv : env ∈ c'.sent - pre.sent) : env.sender = v := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h
  rw [applyNodeStepResult_sent] at henv
  exact (mem_applyEffects_sent_sub v pre _ henv).1

/-- An interrupted reaction changes no corrupted set (the bare framework). -/
theorem CrashDuringStep.adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    c'.adv = pre.adv := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- An interrupted reaction of `v` puts `v` into `crashed` (the bare framework). -/
theorem CrashDuringStep.crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    c'.crashed = insert v pre.crashed := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- An interrupted reaction of `v` leaves every other validator's local state alone (the bare
    framework). -/
theorem CrashDuringStep.other {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') (v' : Node)
    (hv : v' ≠ v) : c'[v'] = pre[v'] := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; exact applyCrashDuring_getElem_other v v' res k pre hv

/-- An interrupted reaction changes no clock (the bare framework). -/
theorem CrashDuringStep.clock {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    c'.clock = pre.clock := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- An interrupted reaction changes no view (the bare framework). -/
theorem CrashDuringStep.view {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    c'.view = pre.view := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; simp

/-- An interrupted reaction of `v` runs from a known local state `l` and leaves `v`'s local state
    known, as `l` with only its disk possibly changed: its memory is the one before the reaction
    (the bare framework). -/
theorem CrashDuringStep.st {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    ∃ (l : Local Node Msg NodeState) (d : NodeState),
      pre[v] = some l ∧ c'[v] = some { l with disk := d } := by
  obtain ⟨l, -, res, hl, -, -, rfl⟩ := h
  obtain ⟨d, hd⟩ := applyCrashDuring_getElem_of_some v v res k pre hl
  exact ⟨l, d, hl, hd⟩

/-- An interrupted reaction keeps an unknown local state unknown, and a known one known (the bare
    framework). -/
theorem CrashDuringStep.getElem_eq_none_iff {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') (v' : Node) :
    c'[v'] = none ↔ pre[v'] = none := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h; exact applyCrashDuring_getElem_eq_none_iff v v' res k pre

/-- An interrupted reaction only adds to the sent log (the bare framework). -/
theorem CrashDuringStep.sent_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c') :
    pre.sent ≤ c'.sent := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h
  rw [applyCrashDuring_sent]; exact applyEffects_sent_le v pre _

/-- Every envelope an interrupted reaction of `v` adds to the sent log is signed by `v` (the bare
    framework). -/
theorem CrashDuringStep.sent_signed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Event Node Msg Ev} {k : Nat}
    {pre c' : Config Node Msg NodeState} (h : CrashDuringStep Pr v e k pre c')
    (env : Envelope Node Msg) (henv : env ∈ c'.sent - pre.sent) : env.sender = v := by
  obtain ⟨-, -, res, -, -, -, rfl⟩ := h
  rw [applyCrashDuring_sent] at henv
  exact (mem_applyEffects_sent_sub v pre _ henv).1

end Framework.RealStsMulticastMultisetLog

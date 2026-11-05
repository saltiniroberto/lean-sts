module
public import RealStsMulticastMultisetLog.Analysis.ReadBacks
public import RealStsMulticastMultisetLog.Spec.Execution
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# What the bare framework's steps and executions do

Theorems about the step relation and the executions of the bare framework `RealStsMulticastMultisetLog`
(`RealStsMulticastMultisetLog.Spec.Protocol`, `RealStsMulticastMultisetLog.Spec.Execution`), kept out of the specification so
that it reads as definitions only. No condition on executions is assumed. The read-backs of the
helpers are on `RealStsMulticastMultisetLog.Analysis.ReadBacks`, which this page imports. In dependency order:

* **The two eliminators.** `Step.elim`, one case per action with the delivery split by whether the
  recipient is corrupted, each case with the enabling condition and the next configuration written
  out; `Step.elimR`, the same cases with the next configuration of a reaction left abstract.
* **The step equations** of `setClock`, `corrupt`, `restart` and a delivery to a corrupted
  validator.
* **Facts per step**, then **per execution**: corruption is permanent; the sent log and the views
  only grow; a clock changes only at its validator's `setClock` and `corrupt`, and never goes back;
  a corrupted validator has no clock and an unknown local state; a validator whose local state is
  known has a clock.
* **Real time.** The stamps never go back and are never negative; finitely many steps up to any
  real time; exactly one configuration in force at every positive real time.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-! ### The eliminators -/

/-- A node action is enabled only at a validator that is up and honest (the bare framework). -/
theorem nodeSpec_enabled {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {na : NodeAction Node Msg Ev}
    {c : Config Node Msg NodeState} (h : (nodeSpec Pr v na).Enabled c) :
    v ∉ c.adv ∧ v ∉ c.crashed :=
  ⟨h.1, h.2.1⟩

/-- A node action is enabled only at a validator whose local state and clock reading are known
    (the bare framework). -/
theorem nodeSpec_enabled_known {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {na : NodeAction Node Msg Ev}
    {c : Config Node Msg NodeState} (h : (nodeSpec Pr v na).Enabled c) :
    ∃ (l : Local Node Msg NodeState) (t : Time), c[v] = some l ∧ c.clock v = some t := by
  obtain ⟨-, -, l, t, hl, ht, -⟩ := h
  exact ⟨l, t, hl, ht⟩

/-- Case analysis on a step of the bare framework, one case per action, the delivery split by
    whether its recipient is corrupted, each case with the action's enabling condition and the next
    configuration written out. A reaction's case binds the local state `l` and the clock reading
    `t` it runs at, and the reaction `res` the protocol permitted.

    Variables: `h`, the step from `c` to `c'` labelled `a`; `motive`, the property to prove of the
    label and the two configurations; one hypothesis per case, proving `motive` of it. -/
theorem Step.elim {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev}
    {motive : Action Node Msg Ev → Config Node Msg NodeState → Config Node Msg NodeState → Prop}
    {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} (h : Step Pr a c c')
    -- the clock of `v`, not corrupted, set to `t`, greater than its reading when it exists
    (setClock : ∀ (d : Config Node Msg NodeState) (v : Node) (t : Time),
      v ∉ d.adv → (∀ r : Time, d.clock v = some r → r < t) →
      motive (.setClock v t) d (Framework.RealStsMulticastMultisetLog.setClock v t d))
    -- the tick of `v`, up and honest, at its clock reading `t`
    (tick : ∀ (d : Config Node Msg NodeState) (v : Node) (l : Local Node Msg NodeState) (t : Time)
        (res : NodeStepResult Node NodeState Msg),
      v ∉ d.adv → v ∉ d.crashed → d[v] = some l → d.clock v = some t →
      Pr.step v t l.st .tick res →
      motive (.tick v) d (applyNodeStepResult Pr v res d))
    -- a delivery to `v`, up and honest, which reacts at its clock reading `t`
    (deliver : ∀ (d : Config Node Msg NodeState) (v : Node) (e : Envelope Node Msg)
        (l : Local Node Msg NodeState) (t : Time) (res : NodeStepResult Node NodeState Msg),
      e ∈ d.sent → e.recipients.Has v → v ∉ d.adv → v ∉ d.crashed → d[v] = some l →
      d.clock v = some t → Pr.step v t l.st (.recv e.toSignedMsg) res →
      motive (.deliver v e) d (applyNodeStepResult Pr v res (receive v e.toSignedMsg d)))
    -- a delivery to `v`, corrupted: the message is filed into `v`'s view only
    (deliverAdv : ∀ (d : Config Node Msg NodeState) (v : Node) (e : Envelope Node Msg),
      e ∈ d.sent → e.recipients.Has v → v ∈ d.adv →
      motive (.deliver v e) d (receive v e.toSignedMsg d))
    -- the corruption of `v`: its local state and its clock emptied
    (corrupt : ∀ (d : Config Node Msg NodeState) (v : Node),
      v ∉ d.adv →
      motive (.corrupt v) d
        { d.setNode v none with
            adv := insert v d.adv
            clock := fun v' => if v = v' then none else d.clock v' })
    -- a crash of `v` between steps
    (crash : ∀ (d : Config Node Msg NodeState) (v : Node),
      v ∉ d.crashed → motive (.crash v) d { d with crashed := insert v d.crashed })
    -- a crash of `v` during the reaction of `na`, at the clock reading `t`, after `k` effects
    (crashDuring : ∀ (d : Config Node Msg NodeState) (v : Node) (na : NodeAction Node Msg Ev)
        (k : Nat) (l : Local Node Msg NodeState) (t : Time)
        (res : NodeStepResult Node NodeState Msg),
      (nodeSpec Pr v na).Enabled d → d[v] = some l → d.clock v = some t →
      Pr.step v t l.st na.event res →
      motive (.crashDuring v na k) d (applyCrashDuring v res k (na.prepare v d)))
    -- the restart of `v`, honest, crashed or never online, at its clock reading `t`
    (restart : ∀ (d : Config Node Msg NodeState) (v : Node) (keep : Bool) (t : Time),
      v ∉ d.adv → (v ∈ d.crashed ∨ d[v] = none) → d.clock v = some t →
      motive (.restart v keep) d
        { d.setNode v (some (match d[v] with
            | some l => { l with st := Pr.restart t keep (if keep then l.st else l.disk) }
            | none => Pr.initialLocal v t))
          with crashed := d.crashed.erase v })
    -- a protocol event at `v`, up and honest, allowed at its clock reading `t`
    (custom : ∀ (d : Config Node Msg NodeState) (v : Node) (ev : Ev) (l : Local Node Msg NodeState)
        (t : Time) (res : NodeStepResult Node NodeState Msg),
      v ∉ d.adv → v ∉ d.crashed → d[v] = some l → d.clock v = some t → Pr.enabled t l.st ev →
      Pr.step v t l.st (.custom ev) res →
      motive (.custom v ev) d (applyNodeStepResult Pr v res d))
    -- an adversarial send by `v`, corrupted
    (adversarial : ∀ (d : Config Node Msg NodeState) (v : Node) (m : Msg)
        (recipients : Recipients Node),
      v ∈ d.adv →
      motive (.adversarial v m recipients) d
        { d with sent := { sender := v, msg := m, recipients := recipients } ::ₘ d.sent }) :
    motive a c c' := by
  obtain ⟨he, hf⟩ := h
  cases a with
  | setClock v t =>
      obtain ⟨h1, h2⟩ := he
      subst hf
      refine setClock c v t h1 fun r hr => ?_
      rw [hr] at h2; exact h2
  | tick v =>
      obtain ⟨h1, h2, -⟩ := he
      obtain ⟨l, t, res, hl, ht, hs, rfl⟩ := hf
      exact tick c v l t res h1 h2 hl ht hs
  | deliver v e =>
      rcases hf with ⟨hadv, rfl⟩ | ⟨hadv, l, t, res, hl, ht, hs, rfl⟩
      · rcases he with ⟨-, h2, h3⟩ | ⟨h1, -⟩
        · exact deliverAdv c v e h2 h3 hadv
        · exact absurd hadv h1
      · rcases he with ⟨h1, -⟩ | ⟨-, h2, -, -, -, -, h3, h4⟩
        · exact absurd h1 hadv
        · exact deliver c v e l t res h3 h4 hadv h2 hl ht hs
  | corrupt v => subst hf; exact corrupt c v he
  | crash v => subst hf; exact crash c v he
  | crashDuring v na k =>
      obtain ⟨l, t, res, hl, ht, hs, rfl⟩ := hf
      rw [NodeAction.prepare_getElem] at hl
      rw [NodeAction.prepare_clock] at ht
      exact crashDuring c v na k l t res he hl ht hs
  | restart v keep =>
      obtain ⟨h1, h2, -⟩ := he
      obtain ⟨t, ht, rfl⟩ := hf
      exact restart c v keep t h1 h2 ht
  | custom v ev =>
      obtain ⟨h1, h2, l, t, hl, ht, hen⟩ := he
      obtain ⟨l', t', res, hl', ht', hs, rfl⟩ := hf
      obtain rfl : l' = l := Option.some_injective _ (hl'.symm.trans hl)
      obtain rfl : t' = t := Option.some_injective _ (ht'.symm.trans ht)
      exact custom c v ev _ _ res h1 h2 hl ht hen hs
  | adversarial v m recipients => subst hf; exact adversarial c v m recipients he

/-- Case analysis on a step of the bare framework, one case per action, the delivery split by
    whether its recipient is corrupted, with the next configuration of a reaction left abstract: a
    completed reaction's case (`tick`, `deliver` to an honest validator, `custom`) is handed its
    enabling condition and the `NodeStep`, an interrupted one's (`crashDuring`) its enabling
    condition and the `CrashDuringStep`. The other cases are those of `Step.elim`.

    Variables: `h`, the step from `c` to `c'` labelled `a`; `motive`, the property to prove of the
    label and the two configurations; one hypothesis per case, proving `motive` of it. -/
theorem Step.elimR {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev}
    {motive : Action Node Msg Ev → Config Node Msg NodeState → Config Node Msg NodeState → Prop}
    {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState} (h : Step Pr a c c')
    -- the clock of `v`, not corrupted, set to `t`, greater than its reading when it exists
    (setClock : ∀ (d : Config Node Msg NodeState) (v : Node) (t : Time),
      v ∉ d.adv → (∀ r : Time, d.clock v = some r → r < t) →
      motive (.setClock v t) d (Framework.RealStsMulticastMultisetLog.setClock v t d))
    -- the tick of `v`, up and honest
    (tick : ∀ (d d' : Config Node Msg NodeState) (v : Node),
      v ∉ d.adv → v ∉ d.crashed → NodeStep Pr v .tick d d' → motive (.tick v) d d')
    -- a delivery to `v`, up and honest, which reacts to it
    (deliver : ∀ (d d' : Config Node Msg NodeState) (v : Node) (e : Envelope Node Msg),
      e ∈ d.sent → e.recipients.Has v → v ∉ d.adv → v ∉ d.crashed →
      NodeStep Pr v (.recv e.toSignedMsg) (receive v e.toSignedMsg d) d' →
      motive (.deliver v e) d d')
    -- a delivery to `v`, corrupted: the message is filed into `v`'s view only
    (deliverAdv : ∀ (d : Config Node Msg NodeState) (v : Node) (e : Envelope Node Msg),
      e ∈ d.sent → e.recipients.Has v → v ∈ d.adv →
      motive (.deliver v e) d (receive v e.toSignedMsg d))
    -- the corruption of `v`: its local state and its clock emptied
    (corrupt : ∀ (d : Config Node Msg NodeState) (v : Node),
      v ∉ d.adv →
      motive (.corrupt v) d
        { d.setNode v none with
            adv := insert v d.adv
            clock := fun v' => if v = v' then none else d.clock v' })
    -- a crash of `v` between steps
    (crash : ∀ (d : Config Node Msg NodeState) (v : Node),
      v ∉ d.crashed → motive (.crash v) d { d with crashed := insert v d.crashed })
    -- a crash of `v` during the reaction of `na`, after `k` effects
    (crashDuring : ∀ (d d' : Config Node Msg NodeState) (v : Node) (na : NodeAction Node Msg Ev)
        (k : Nat),
      (nodeSpec Pr v na).Enabled d → CrashDuringStep Pr v na.event k (na.prepare v d) d' →
      motive (.crashDuring v na k) d d')
    -- the restart of `v`, honest, crashed or never online, at its clock reading `t`
    (restart : ∀ (d : Config Node Msg NodeState) (v : Node) (keep : Bool) (t : Time),
      v ∉ d.adv → (v ∈ d.crashed ∨ d[v] = none) → d.clock v = some t →
      motive (.restart v keep) d
        { d.setNode v (some (match d[v] with
            | some l => { l with st := Pr.restart t keep (if keep then l.st else l.disk) }
            | none => Pr.initialLocal v t))
          with crashed := d.crashed.erase v })
    -- a protocol event at `v`, up and honest, allowed at its clock reading
    (custom : ∀ (d d' : Config Node Msg NodeState) (v : Node) (ev : Ev),
      v ∉ d.adv → v ∉ d.crashed →
      (∃ (l : Local Node Msg NodeState) (t : Time),
        d[v] = some l ∧ d.clock v = some t ∧ Pr.enabled t l.st ev) →
      NodeStep Pr v (.custom ev) d d' → motive (.custom v ev) d d')
    -- an adversarial send by `v`, corrupted
    (adversarial : ∀ (d : Config Node Msg NodeState) (v : Node) (m : Msg)
        (recipients : Recipients Node),
      v ∈ d.adv →
      motive (.adversarial v m recipients) d
        { d with sent := { sender := v, msg := m, recipients := recipients } ::ₘ d.sent }) :
    motive a c c' := by
  obtain ⟨he, hf⟩ := h
  cases a with
  | setClock v t =>
      obtain ⟨h1, h2⟩ := he
      subst hf
      refine setClock c v t h1 fun r hr => ?_
      rw [hr] at h2; exact h2
  | tick v => exact tick c c' v he.1 he.2.1 hf
  | deliver v e =>
      rcases hf with ⟨hadv, rfl⟩ | ⟨hadv, hf⟩
      · rcases he with ⟨-, h2, h3⟩ | ⟨h1, -⟩
        · exact deliverAdv c v e h2 h3 hadv
        · exact absurd hadv h1
      · rcases he with ⟨h1, -⟩ | ⟨-, h2, -, -, -, -, h3, h4⟩
        · exact absurd h1 hadv
        · exact deliver c c' v e h3 h4 hadv h2 hf
  | corrupt v => subst hf; exact corrupt c v he
  | crash v => subst hf; exact crash c v he
  | crashDuring v na k => exact crashDuring c c' v na k he hf
  | restart v keep =>
      obtain ⟨h1, h2, -⟩ := he
      obtain ⟨t, ht, rfl⟩ := hf
      exact restart c v keep t h1 h2 ht
  | custom v ev =>
      obtain ⟨h1, h2, l, t, hl, ht, hen⟩ := he
      exact custom c c' v ev h1 h2 ⟨l, t, hl, ht, hen⟩ hf
  | adversarial v m recipients => subst hf; exact adversarial c v m recipients he

/-! ### The step equations -/

/-- A `setClock v t` step is taken only at a validator `v` not corrupted whose clock, when it
    exists, reads less than `t`, and its next configuration is `setClock v t c` (the bare
    framework). -/
theorem Step.setClock_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {t : Time} {c c' : Config Node Msg NodeState}
    (h : Step Pr (.setClock v t) c c') :
    v ∉ c.adv ∧ (∀ r : Time, c.clock v = some r → r < t) ∧ c' = setClock v t c := by
  obtain ⟨⟨h1, h2⟩, rfl⟩ := h
  refine ⟨h1, fun r hr => ?_, rfl⟩
  rw [hr] at h2; exact h2

/-- A `corrupt v` step is taken only at a validator `v` not corrupted; it puts `v` into the
    corrupted set and empties `v`'s local state and clock, and changes nothing else (the bare
    framework). -/
theorem Step.corrupt_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {c c' : Config Node Msg NodeState}
    (h : Step Pr (.corrupt v) c c') :
    v ∉ c.adv ∧ c'[v] = none ∧ c'.clock v = none ∧
      (∀ v' : Node, v' ≠ v → c'[v'] = c[v'] ∧ c'.clock v' = c.clock v') ∧
      c'.view = c.view ∧ c'.adv = insert v c.adv ∧ c'.crashed = c.crashed ∧
      c'.sent = c.sent := by
  obtain ⟨h1, rfl⟩ := h
  refine ⟨h1, Config.setNode_self v none c, if_pos rfl, fun v' hv => ⟨?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · exact Config.setNode_other v v' none c hv
  · exact if_neg (Ne.symm hv)

/-- A `restart v keep` step is taken only at a validator `v` not corrupted, crashed or with its
    local state unknown, whose clock reads some `t`. It takes `v` out of `crashed`; `v`'s local
    state becomes `Pr.restart t keep` of its memory (`keep = true`) or of its disk (`keep = false`),
    the disk kept, when it was known, and `Pr.initialLocal v t` when it was unknown; nothing else
    changes (the bare framework). -/
theorem Step.restart_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {keep : Bool}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.restart v keep) c c') :
    v ∉ c.adv ∧ (v ∈ c.crashed ∨ c[v] = none) ∧
      ∃ t : Time, c.clock v = some t ∧
        c'[v] = some (match c[v] with
          | some l => { l with st := Pr.restart t keep (if keep then l.st else l.disk) }
          | none => Pr.initialLocal v t) ∧
        (∀ v' : Node, v' ≠ v → c'[v'] = c[v']) ∧ c'.clock = c.clock ∧ c'.view = c.view ∧
        c'.crashed = c.crashed.erase v ∧ c'.adv = c.adv ∧ c'.sent = c.sent := by
  obtain ⟨⟨h1, h2, -⟩, t, ht, rfl⟩ := h
  exact ⟨h1, h2, t, ht, Config.setNode_self v _ c,
    fun v' hv => Config.setNode_other v v' _ c hv, rfl, rfl, rfl, rfl, rfl⟩

/-- A restart of `v` whose local state `l` is known, with the clock reading `t`, leaves `v`'s local
    state `l` with the memory `Pr.restart t keep` of its memory (`keep = true`) or of its disk
    (`keep = false`) (the bare framework). -/
theorem Step.restart_getElem_of_some {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {v : Node} {keep : Bool}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.restart v keep) c c')
    {l : Local Node Msg NodeState} (hl : c[v] = some l) {t : Time} (ht : c.clock v = some t) :
    c'[v] = some { l with st := Pr.restart t keep (if keep then l.st else l.disk) } := by
  obtain ⟨-, -, t', ht', h', -⟩ := h.restart_eq
  obtain rfl : t' = t := Option.some_injective _ (ht'.symm.trans ht)
  rw [h', hl]

/-- A restart of `v` whose local state is unknown, with the clock reading `t`, brings `v` online
    with the local state `Pr.initialLocal v t` (the bare framework). -/
theorem Step.restart_getElem_of_none {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {v : Node} {keep : Bool}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.restart v keep) c c') (hl : c[v] = none)
    {t : Time} (ht : c.clock v = some t) : c'[v] = some (Pr.initialLocal v t) := by
  obtain ⟨-, -, t', ht', h', -⟩ := h.restart_eq
  obtain rfl : t' = t := Option.some_injective _ (ht'.symm.trans ht)
  rw [h', hl]

/-- A delivery to a corrupted validator `v` is taken only when the envelope is on the wire and
    names `v`; it files the envelope's signed message into `v`'s view, and changes nothing else
    (the bare framework). -/
theorem Step.deliver_eq_of_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Envelope Node Msg}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.deliver v e) c c') (hv : v ∈ c.adv) :
    e ∈ c.sent ∧ e.recipients.Has v ∧ c' = receive v e.toSignedMsg c := by
  obtain ⟨he, hf⟩ := h
  rcases hf with ⟨-, rfl⟩ | ⟨hadv, -⟩
  · rcases he with ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · exact ⟨h2, h3, rfl⟩
    · exact absurd hv h1
  · exact absurd hv hadv

/-- A delivery is taken only when the envelope is on the wire and names its recipient (the bare
    framework). -/
theorem Step.deliver_sent {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Envelope Node Msg}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.deliver v e) c c') :
    e ∈ c.sent ∧ e.recipients.Has v := by
  rcases h.1 with ⟨-, h2, h3⟩ | ⟨-, -, -, -, -, -, h2, h3⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h2, h3⟩

/-- A delivery to an honest validator `v` is taken only when `v` is up, with its local state and
    clock reading known (the bare framework). -/
theorem Step.deliver_up_of_not_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {v : Node} {e : Envelope Node Msg}
    {c c' : Config Node Msg NodeState} (h : Step Pr (.deliver v e) c c') (hv : v ∉ c.adv) :
    v ∉ c.crashed ∧
      ∃ (l : Local Node Msg NodeState) (t : Time), c[v] = some l ∧ c.clock v = some t := by
  rcases h.1 with ⟨h1, -⟩ | he
  · exact absurd h1 hv
  · exact ⟨(nodeSpec_enabled he).2, nodeSpec_enabled_known he⟩

/-! ### Facts by construction, per step -/

/-- Corruption is permanent: the corrupted set only grows (the bare framework). -/
theorem Step.adv_subset {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') : c.adv ⊆ c'.adv := by
  refine h.elim (motive := fun _ d d' => d.adv ⊆ d'.adv)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom ?adversarial
  case corrupt => intros; exact Finset.subset_insert _ _
  all_goals intros; simp

/-- The corrupted set changes only at a `corrupt` step (the bare framework). -/
theorem Step.adv_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') (ha : ∀ v : Node, a ≠ .corrupt v) :
    c'.adv = c.adv := by
  refine h.elim (motive := fun a d d' => (∀ v : Node, a ≠ .corrupt v) → d'.adv = d.adv)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial ha
  case corrupt => intro d v _ hv; exact absurd rfl (hv v)
  all_goals intros; simp

/-- The sent log only grows (the bare framework). -/
theorem Step.sent_le {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') : c.sent ≤ c'.sent := by
  refine h.elim (motive := fun _ d d' => d.sent ≤ d'.sent)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom ?adversarial
  case tick =>
    intro d v _ _ res _ _ _ _ _
    rw [applyNodeStepResult_sent]; exact applyEffects_sent_le v d _
  case deliver =>
    intro d v e _ _ res _ _ _ _ _ _ _
    rw [applyNodeStepResult_sent, ← receive_sent v e.toSignedMsg d]
    exact applyEffects_sent_le v _ _
  case crashDuring =>
    intro d v na k _ _ res _ _ _ _
    rw [applyCrashDuring_sent, ← NodeAction.prepare_sent v d na]
    exact applyEffects_sent_le v _ _
  case custom =>
    intro d v ev _ _ res _ _ _ _ _ _
    rw [applyNodeStepResult_sent]; exact applyEffects_sent_le v d _
  case adversarial => intros; exact Multiset.le_cons_self _ _
  all_goals intros; exact le_rfl

/-- Every view only grows (the bare framework). -/
theorem Step.view_subset {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') (v : Node) :
    c.view v ⊆ c'.view v := by
  refine h.elim (motive := fun _ d d' => d.view v ⊆ d'.view v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom ?adversarial
  case deliver =>
    intro d w e _ _ _ _ _ _ _ _ _ _
    rw [applyNodeStepResult_view, receive_view]
    split_ifs with hw
    · subst hw; exact Finset.subset_insert _ _
    · exact subset_rfl
  case deliverAdv =>
    intro d w e _ _ _
    rw [receive_view]
    split_ifs with hw
    · subst hw; exact Finset.subset_insert _ _
    · exact subset_rfl
  case crashDuring =>
    intro d w na k _ _ _ _ _ _ _
    rw [applyCrashDuring_view]
    by_cases hw : v = w
    · subst hw
      cases na with
      | tick => exact subset_rfl
      | deliver e => rw [NodeAction.prepare_deliver, receive_view_self]; exact Finset.subset_insert _ _
      | custom ev => exact subset_rfl
    · rw [NodeAction.prepare_view_other w v d na hw]
  all_goals intros; simp

/-- A validator's view changes only at a delivery to it (the bare framework). -/
theorem Step.view_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (hdeliver : ∀ e : Envelope Node Msg, a ≠ .deliver v e)
    (hcd : ∀ (e : Envelope Node Msg) (k : Nat), a ≠ .crashDuring v (.deliver e) k) :
    c'.view v = c.view v := by
  refine h.elim (motive := fun a d d' => (∀ e : Envelope Node Msg, a ≠ .deliver v e) →
      (∀ (e : Envelope Node Msg) (k : Nat), a ≠ .crashDuring v (.deliver e) k) →
      d'.view v = d.view v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hdeliver hcd
  case deliver =>
    intro d w e _ _ _ _ _ _ _ _ _ _ hne _
    have hvw : v ≠ w := fun hvw => hne e (by rw [hvw])
    rw [applyNodeStepResult_view, receive_view_other w v _ d hvw]
  case deliverAdv =>
    intro d w e _ _ _ hne _
    have hvw : v ≠ w := fun hvw => hne e (by rw [hvw])
    rw [receive_view_other w v _ d hvw]
  case crashDuring =>
    intro d w na k _ _ _ _ _ _ _ _ hne
    rw [applyCrashDuring_view]
    by_cases hvw : v = w
    · subst hvw
      cases na with
      | tick => rfl
      | deliver e => exact absurd rfl (hne e k)
      | custom ev => rfl
    · exact NodeAction.prepare_view_other w v d na hvw
  all_goals intros; simp

/-- The steps `tick`, `custom` and `crashDuring` of `v` are taken only at a validator `v` that is
    up and honest, with its local state and clock reading known (the bare framework). -/
theorem Step.up_honest {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (ha : a = .tick v ∨ (∃ ev : Ev, a = .custom v ev) ∨
      ∃ (na : NodeAction Node Msg Ev) (k : Nat), a = .crashDuring v na k) :
    v ∉ c.adv ∧ v ∉ c.crashed ∧
      ∃ (l : Local Node Msg NodeState) (t : Time), c[v] = some l ∧ c.clock v = some t := by
  obtain ⟨he, -⟩ := h
  rcases ha with rfl | ⟨ev, rfl⟩ | ⟨na, k, rfl⟩
  · exact ⟨(nodeSpec_enabled (na := .tick) he).1, (nodeSpec_enabled (na := .tick) he).2,
      nodeSpec_enabled_known (na := .tick) he⟩
  · exact ⟨(nodeSpec_enabled (na := .custom ev) he).1,
      (nodeSpec_enabled (na := .custom ev) he).2, nodeSpec_enabled_known (na := .custom ev) he⟩
  · exact ⟨(nodeSpec_enabled (na := na) he).1, (nodeSpec_enabled (na := na) he).2,
      nodeSpec_enabled_known (na := na) he⟩

/-- A crashed validator leaves `crashed` only by its `restart` (the bare framework). -/
theorem Step.mem_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node} (hv : v ∈ c.crashed)
    (ha : ∀ keep : Bool, a ≠ .restart v keep) : v ∈ c'.crashed := by
  refine h.elim (motive := fun a d d' =>
      v ∈ d.crashed → (∀ keep : Bool, a ≠ .restart v keep) → v ∈ d'.crashed)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hv ha
  case restart =>
    intro d w keep _ _ _ _ hvd hne
    have hvw : v ≠ w := fun hvw => hne keep (by rw [hvw])
    exact Finset.mem_erase.2 ⟨hvw, hvd⟩
  case crash => intro d w _ hvd _; exact Finset.mem_insert_of_mem hvd
  case crashDuring =>
    intro d w na k _ _ _ _ _ _ _ hvd _
    rw [applyCrashDuring_crashed, NodeAction.prepare_crashed]
    exact Finset.mem_insert_of_mem hvd
  all_goals intros; simp_all

/-- An up validator joins `crashed` only by a `crash` or a `crashDuring` of its own (the bare
    framework). -/
theorem Step.not_mem_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node} (hv : v ∉ c.crashed)
    (hcrash : a ≠ .crash v)
    (hcd : ∀ (na : NodeAction Node Msg Ev) (k : Nat), a ≠ .crashDuring v na k) :
    v ∉ c'.crashed := by
  refine h.elim (motive := fun a d d' =>
      v ∉ d.crashed → a ≠ .crash v →
        (∀ (na : NodeAction Node Msg Ev) (k : Nat), a ≠ .crashDuring v na k) →
        v ∉ d'.crashed)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hv hcrash hcd
  case crash =>
    intro d w _ hvd hne
    have hvw : v ≠ w := fun hvw => hne (by rw [hvw])
    simpa [hvw] using hvd
  case crashDuring =>
    intro d w na k _ _ _ _ _ _ _ hvd _ hne
    have hvw : v ≠ w := fun hvw => hne na k (by rw [hvw])
    rw [applyCrashDuring_crashed, NodeAction.prepare_crashed]
    simpa [hvw] using hvd
  case restart =>
    intro d w keep _ _ _ _ hvd _ _
    exact fun hm => hvd (Finset.mem_of_mem_erase hm)
  all_goals intros; simp_all

/-- A validator's local state changes only at its own steps that run a reaction, its corruption
    and its restart: a step that is none of `tick v`, `deliver v e`, `custom v ev`,
    `crashDuring v na k`, `corrupt v`, `restart v keep` leaves `c[v]` as it was (the bare
    framework). -/
theorem Step.getElem_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (htick : a ≠ .tick v) (hdeliver : ∀ e : Envelope Node Msg, a ≠ .deliver v e)
    (hcustom : ∀ ev : Ev, a ≠ .custom v ev)
    (hcd : ∀ (na : NodeAction Node Msg Ev) (k : Nat), a ≠ .crashDuring v na k)
    (hcorrupt : a ≠ .corrupt v) (hrestart : ∀ keep : Bool, a ≠ .restart v keep) :
    c'[v] = c[v] := by
  refine h.elim (motive := fun a d d' =>
      a ≠ .tick v → (∀ e : Envelope Node Msg, a ≠ .deliver v e) → (∀ ev : Ev, a ≠ .custom v ev) →
      (∀ (na : NodeAction Node Msg Ev) (k : Nat), a ≠ .crashDuring v na k) →
      a ≠ .corrupt v → (∀ keep : Bool, a ≠ .restart v keep) → d'[v] = d[v])
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial htick hdeliver hcustom hcd hcorrupt hrestart
  case tick =>
    intro d w _ _ res _ _ _ _ _ hne _ _ _ _ _
    have hvw : v ≠ w := fun hvw => hne (by rw [hvw])
    exact applyNodeStepResult_getElem_other Pr w v res d hvw
  case deliver =>
    intro d w e _ _ res _ _ _ _ _ _ _ _ hne _ _ _ _
    have hvw : v ≠ w := fun hvw => hne e (by rw [hvw])
    rw [applyNodeStepResult_getElem_other Pr w v res _ hvw, receive_getElem]
  case corrupt =>
    intro d w _ _ _ _ _ hne _
    have hvw : v ≠ w := fun hvw => hne (by rw [hvw])
    exact Config.setNode_other w v none d hvw
  case crashDuring =>
    intro d w na k _ _ res _ _ _ _ _ _ _ hne _ _
    have hvw : v ≠ w := fun hvw => hne na k (by rw [hvw])
    rw [applyCrashDuring_getElem_other w v res k _ hvw, NodeAction.prepare_getElem]
  case restart =>
    intro d w keep _ _ _ _ _ _ _ _ _ hne
    have hvw : v ≠ w := fun hvw => hne keep (by rw [hvw])
    exact Config.setNode_other w v _ d hvw
  case custom =>
    intro d w ev _ _ res _ _ _ _ _ _ _ _ hne _ _ _
    have hvw : v ≠ w := fun hvw => hne ev (by rw [hvw])
    exact applyNodeStepResult_getElem_other Pr w v res d hvw
  all_goals intros; rfl

/-- A crashed validator's local state is unchanged by every step but its own corruption and its
    own restart (the bare framework). -/
theorem Step.getElem_of_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node} (hv : v ∈ c.crashed)
    (hcorrupt : a ≠ .corrupt v) (hrestart : ∀ keep : Bool, a ≠ .restart v keep) :
    c'[v] = c[v] := by
  refine h.elim (motive := fun a d d' =>
      v ∈ d.crashed → a ≠ .corrupt v → (∀ keep : Bool, a ≠ .restart v keep) → d'[v] = d[v])
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hv hcorrupt hrestart
  case tick =>
    intro d w _ _ res _ hw _ _ _ hvd _ _
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hvd)
    exact applyNodeStepResult_getElem_other Pr w v res d hvw
  case deliver =>
    intro d w e _ _ res _ _ _ hw _ _ _ hvd _ _
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hvd)
    rw [applyNodeStepResult_getElem_other Pr w v res _ hvw, receive_getElem]
  case corrupt =>
    intro d w _ _ hne _
    have hvw : v ≠ w := fun hvw => hne (by rw [hvw])
    exact Config.setNode_other w v none d hvw
  case crashDuring =>
    intro d w na k _ _ res hen _ _ _ hvd _ _
    have hvw : v ≠ w := fun hvw => (nodeSpec_enabled hen).2 (hvw ▸ hvd)
    rw [applyCrashDuring_getElem_other w v res k _ hvw, NodeAction.prepare_getElem]
  case restart =>
    intro d w keep _ _ _ _ _ _ hne
    have hvw : v ≠ w := fun hvw => hne keep (by rw [hvw])
    exact Config.setNode_other w v _ d hvw
  case custom =>
    intro d w ev _ _ res _ hw _ _ _ _ hvd _ _
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hvd)
    exact applyNodeStepResult_getElem_other Pr w v res d hvw
  all_goals intros; rfl

/-- A validator's clock changes only at its own `setClock` and its own corruption (the bare
    framework). -/
theorem Step.clock_eq {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (hset : ∀ t : Time, a ≠ .setClock v t) (hcorrupt : a ≠ .corrupt v) :
    c'.clock v = c.clock v := by
  refine h.elim (motive := fun a d d' =>
      (∀ t : Time, a ≠ .setClock v t) → a ≠ .corrupt v → d'.clock v = d.clock v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hset hcorrupt
  case setClock =>
    intro d w t _ _ hne _
    have hvw : v ≠ w := fun hvw => hne t (by rw [hvw])
    exact setClock_clock_other w v t d hvw
  case corrupt =>
    intro d w _ _ hne
    have hvw : v ≠ w := fun hvw => hne (by rw [hvw])
    exact if_neg (Ne.symm hvw)
  all_goals intros; simp

/-- A step never sets a clock back: when `v`'s clock reads `t` before the step and `t'` after it,
    `t ≤ t'` (the bare framework). -/
theorem Step.clock_le {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node} {t t' : Time}
    (ht : c.clock v = some t) (ht' : c'.clock v = some t') : t ≤ t' := by
  by_cases hset : ∃ t'' : Time, a = .setClock v t''
  · obtain ⟨t'', rfl⟩ := hset
    obtain ⟨-, hlt, rfl⟩ := h.setClock_eq
    rw [setClock_clock_self] at ht'
    obtain rfl := Option.some_injective _ ht'
    exact le_of_lt (hlt t ht)
  by_cases hcor : a = .corrupt v
  · subst hcor
    obtain ⟨-, -, hnone, -⟩ := h.corrupt_eq
    rw [hnone] at ht'; exact absurd ht' (by simp)
  push Not at hset
  rw [h.clock_eq hset hcor, ht] at ht'
  exact le_of_eq (Option.some_injective _ ht')

/-- A clock that exists becomes absent only at its validator's corruption: when `v`'s clock exists
    before the step and not after it, `v` is corrupted after it (the bare framework). -/
theorem Step.mem_adv_of_clock_eq_none {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (ht : c.clock v ≠ none) (ht' : c'.clock v = none) : v ∈ c'.adv := by
  by_cases hset : ∃ t'' : Time, a = .setClock v t''
  · obtain ⟨t'', rfl⟩ := hset
    obtain ⟨-, -, rfl⟩ := h.setClock_eq
    rw [setClock_clock_self] at ht'; exact absurd ht' (by simp)
  by_cases hcor : a = .corrupt v
  · subst hcor
    obtain ⟨-, -, -, -, -, hadv, -⟩ := h.corrupt_eq
    rw [hadv]; exact Finset.mem_insert_self v _
  push Not at hset
  rw [h.clock_eq hset hcor] at ht'
  exact absurd ht' ht

/-- After a completed reaction of `v` (a `tick` or `custom` step of `v`, or a delivery to `v`
    while honest), `v`'s local state is known and its disk is `Pr.persist` of its memory (the bare
    framework). -/
theorem Step.disk_eq_persist {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (ha : a = .tick v ∨ (∃ ev : Ev, a = .custom v ev) ∨
      ∃ e : Envelope Node Msg, a = .deliver v e ∧ v ∉ c.adv) :
    ∃ l : Local Node Msg NodeState, c'[v] = some l ∧ l.disk = Pr.persist l.st := by
  obtain ⟨-, hf⟩ := h
  rcases ha with rfl | ⟨ev, rfl⟩ | ⟨e, rfl, hv⟩
  · exact NodeStep.disk hf
  · exact NodeStep.disk hf
  · rcases hf with ⟨hadv, -⟩ | ⟨-, hf⟩
    · exact absurd hadv hv
    · exact NodeStep.disk hf

/-- A validator is corrupted after a step only if it was corrupted before it, or the step is its
    corruption (the bare framework). -/
theorem Step.mem_adv_or_corrupt {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node} (hv : v ∈ c'.adv) :
    v ∈ c.adv ∨ a = .corrupt v := by
  refine h.elim (motive := fun a d d' => v ∈ d'.adv → v ∈ d.adv ∨ a = .corrupt v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hv
  case corrupt =>
    intro d w _ hv'
    rcases Finset.mem_insert.1 hv' with rfl | hv'
    · exact Or.inr rfl
    · exact Or.inl hv'
  all_goals intros; simp_all

/-- One step keeps "a corrupted validator has no clock": if it holds of `v` before the step, it
    holds of `v` after it (the bare framework). -/
theorem Step.clock_eq_none_of_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (hinv : v ∈ c.adv → c.clock v = none) : v ∈ c'.adv → c'.clock v = none := by
  intro hv'
  by_cases hcor : a = .corrupt v
  · subst hcor
    exact h.corrupt_eq.2.2.1
  have hv : v ∈ c.adv := (h.mem_adv_or_corrupt hv').resolve_right hcor
  by_cases hset : ∃ t : Time, a = .setClock v t
  · obtain ⟨t, rfl⟩ := hset
    exact absurd hv h.setClock_eq.1
  push Not at hset
  rw [h.clock_eq hset hcor]
  exact hinv hv

/-- One step keeps "a corrupted validator's local state is unknown": if it holds of `v` before
    the step, it holds of `v` after it (the bare framework). -/
theorem Step.getElem_eq_none_of_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (hinv : v ∈ c.adv → c[v] = none) : v ∈ c'.adv → c'[v] = none := by
  refine h.elim (motive := fun _ d d' => (v ∈ d.adv → d[v] = none) → v ∈ d'.adv → d'[v] = none)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hinv
  case tick =>
    intro d w _ _ res hw _ _ _ _ hinv hv'
    rw [applyNodeStepResult_adv] at hv'
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hv')
    rw [applyNodeStepResult_getElem_other Pr w v res d hvw]; exact hinv hv'
  case deliver =>
    intro d w e _ _ res _ _ hw _ _ _ _ hinv hv'
    rw [applyNodeStepResult_adv, receive_adv] at hv'
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hv')
    rw [applyNodeStepResult_getElem_other Pr w v res _ hvw, receive_getElem]; exact hinv hv'
  case corrupt =>
    intro d w _ hinv hv'
    by_cases hvw : v = w
    · subst hvw; exact Config.setNode_self v none d
    · exact (Config.setNode_other w v none d hvw).trans
        (hinv ((Finset.mem_insert.1 hv').resolve_left hvw))
  case crashDuring =>
    intro d w na k _ _ res hen _ _ _ hinv hv'
    rw [applyCrashDuring_adv, NodeAction.prepare_adv] at hv'
    have hvw : v ≠ w := fun hvw => (nodeSpec_enabled hen).1 (hvw ▸ hv')
    rw [applyCrashDuring_getElem_other w v res k _ hvw, NodeAction.prepare_getElem]
    exact hinv hv'
  case restart =>
    intro d w keep _ hw _ _ hinv hv'
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hv')
    exact (Config.setNode_other w v _ d hvw).trans (hinv hv')
  case custom =>
    intro d w ev _ _ res hw _ _ _ _ _ hinv hv'
    rw [applyNodeStepResult_adv] at hv'
    have hvw : v ≠ w := fun hvw => hw (hvw ▸ hv')
    rw [applyNodeStepResult_getElem_other Pr w v res d hvw]; exact hinv hv'
  all_goals (intros; rename_i hinv hv'; exact hinv hv')

/-- One step keeps "a validator whose local state is known has a clock": if it holds of `v`
    before the step, it holds of `v` after it (the bare framework). -/
theorem Step.clock_ne_none_of_getElem_ne_none {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {a : Action Node Msg Ev}
    {c c' : Config Node Msg NodeState} (h : Step Pr a c c') {v : Node}
    (hinv : c[v] ≠ none → c.clock v ≠ none) : c'[v] ≠ none → c'.clock v ≠ none := by
  refine h.elim (motive := fun _ d d' =>
      (d[v] ≠ none → d.clock v ≠ none) → d'[v] ≠ none → d'.clock v ≠ none)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hinv
  case setClock =>
    intro d w t _ _ hinv hv'
    by_cases hvw : v = w
    · subst hvw; rw [setClock_clock_self]; exact Option.some_ne_none t
    · rw [setClock_clock_other w v t d hvw]; exact hinv hv'
  case tick =>
    intro d w _ _ res _ _ _ _ _ hinv hv'
    rw [applyNodeStepResult_clock]
    exact hinv fun hn => hv' ((applyNodeStepResult_getElem_eq_none_iff Pr w v res d).2 hn)
  case deliver =>
    intro d w e _ _ res _ _ _ _ _ _ _ hinv hv'
    rw [applyNodeStepResult_clock, receive_clock]
    exact hinv fun hn => hv' ((applyNodeStepResult_getElem_eq_none_iff Pr w v res _).2 hn)
  case corrupt =>
    intro d w _ hinv hv'
    by_cases hvw : v = w
    · subst hvw; exact absurd (Config.setNode_self v none d) hv'
    · show (if w = v then none else d.clock v) ≠ none
      rw [if_neg (Ne.symm hvw)]
      exact hinv fun hn => hv' ((Config.setNode_other w v none d hvw).trans hn)
  case crashDuring =>
    intro d w na k _ _ res _ _ _ _ hinv hv'
    rw [applyCrashDuring_clock, NodeAction.prepare_clock]
    refine hinv fun hn => hv' ((applyCrashDuring_getElem_eq_none_iff w v res k _).2 ?_)
    rw [NodeAction.prepare_getElem]; exact hn
  case restart =>
    intro d w keep t _ _ ht hinv hv'
    show d.clock v ≠ none
    by_cases hvw : v = w
    · subst hvw; rw [ht]; exact Option.some_ne_none t
    · exact hinv fun hn => hv' ((Config.setNode_other w v _ d hvw).trans hn)
  case custom =>
    intro d w ev _ _ res _ _ _ _ _ _ hinv hv'
    rw [applyNodeStepResult_clock]
    exact hinv fun hn => hv' ((applyNodeStepResult_getElem_eq_none_iff Pr w v res d).2 hn)
  all_goals (intros; rename_i hinv hv'; exact hinv hv')

/-! ### Facts by construction, per execution -/

/-- The step of `x` at `i`, in the bare framework's step relation. -/
theorem Execution.step_at {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) :
    Step Pr (x.lbl i) x[i] x[i + 1] :=
  x.step i

/-- Corruption is permanent along an execution (the bare framework). -/
theorem Execution.adv_mono {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} (hij : i ≤ j) :
    x[i].adv ⊆ x[j].adv := by
  induction hij with
  | refl => exact subset_rfl
  | @step j' _ ih => exact ih.trans (x.step_at j').adv_subset

/-- The sent log only grows along an execution (the bare framework). -/
theorem Execution.sent_mono {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} (hij : i ≤ j) :
    x[i].sent ≤ x[j].sent := by
  induction hij with
  | refl => exact le_rfl
  | @step j' _ ih => exact ih.trans (x.step_at j').sent_le

/-- Every view only grows along an execution (the bare framework). -/
theorem Execution.view_mono {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (v : Node) {i j : Nat} (hij : i ≤ j) :
    x[i].view v ⊆ x[j].view v := by
  induction hij with
  | refl => exact subset_rfl
  | @step j' _ ih => exact ih.trans ((x.step_at j').view_subset v)

/-- A validator crashed after `i` steps has the same local state after `i + 1` steps unless step
    `i` is its corruption or its restart (the bare framework). -/
theorem Execution.getElem_succ_of_crashed {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i : Nat} {v : Node}
    (hv : v ∈ x[i].crashed) (hcorrupt : x.lbl i ≠ .corrupt v)
    (hrestart : ∀ keep : Bool, x.lbl i ≠ .restart v keep) : x[i + 1][v] = x[i][v] :=
  (x.step_at i).getElem_of_crashed hv hcorrupt hrestart

/-- A validator's clock changes at step `i` only if step `i` is its `setClock` or its corruption
    (the bare framework). -/
theorem Execution.clock_succ {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i : Nat} {v : Node}
    (hset : ∀ t : Time, x.lbl i ≠ .setClock v t) (hcorrupt : x.lbl i ≠ .corrupt v) :
    x[i + 1].clock v = x[i].clock v :=
  (x.step_at i).clock_eq hset hcorrupt

/-! ### Real time -/

/-- The run starts at the real time `0` (the bare framework). -/
@[simp] theorem Execution.stamp_zero {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) : x.stamp 0 = 0 :=
  x.init_stamp

/-- The real time never goes back along an execution: a later configuration is entered no earlier
    (the bare framework). -/
theorem Execution.stamp_mono {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} (hij : i ≤ j) :
    x.stamp i ≤ x.stamp j := by
  induction hij with
  | refl => exact le_rfl
  | @step j' _ ih => exact ih.trans (x.mono j')

/-- No configuration is entered at a negative real time (the bare framework). -/
theorem Execution.stamp_nonneg {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) :
    0 ≤ x.stamp i := by
  have h := x.stamp_mono (Nat.zero_le i)
  rwa [x.stamp_zero] at h

/-- Every real time `r` is strictly exceeded by some configuration's stamp (the bare framework). -/
theorem Execution.exists_stamp_gt {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (r : ℝ) :
    ∃ i : Nat, r < x.stamp i := by
  obtain ⟨i, hi⟩ := x.progress (r + 1)
  exact ⟨i, by linarith⟩

/-- Finitely many configurations are entered at or before any real time `r` (the bare
    framework). -/
theorem Execution.finite_stamp_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (r : ℝ) :
    {i : Nat | x.stamp i ≤ r}.Finite := by
  obtain ⟨N, hN⟩ := x.exists_stamp_gt r
  refine (Set.finite_lt_nat N).subset fun i (hi : x.stamp i ≤ r) => ?_
  show i < N
  by_contra h
  have := x.stamp_mono (not_lt.1 h)
  linarith

/-- Finitely many steps are taken at or before any real time `r`; step `i` is taken at
    `x.stamp (i + 1)` (the bare framework). -/
theorem Execution.finite_steps_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (r : ℝ) :
    {i : Nat | x.stamp (i + 1) ≤ r}.Finite :=
  (x.finite_stamp_le r).subset fun i (hi : x.stamp (i + 1) ≤ r) => (x.mono i).trans hi

/-- Finitely many steps are taken inside any real window `[r, r']` (the bare framework). -/
theorem Execution.finite_steps_within {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (r r' : ℝ) :
    {i : Nat | r ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ r'}.Finite :=
  (x.finite_steps_le r').subset fun _ hi => hi.2

/-- At every positive real time `s` some configuration is in force: the one before the first
    configuration entered at `s` or later (the bare framework). -/
theorem Execution.exists_inForce {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {s : ℝ} (hs : 0 < s) :
    ∃ i : Nat, x.InForce i s := by
  classical
  have h : ∃ n : Nat, s ≤ x.stamp n := x.progress s
  have hN := Nat.find_spec h
  have hN0 : Nat.find h ≠ 0 := by
    intro h0
    rw [h0, x.stamp_zero] at hN
    linarith
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  refine ⟨M, ?_, ?_⟩
  · have := Nat.find_min h (show M < Nat.find h by omega)
    exact lt_of_not_ge this
  · rw [hM] at hN; exact hN

/-- At most one configuration is in force at a real time (the bare framework). -/
theorem Execution.inForce_unique {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} {s : ℝ}
    (hi : x.InForce i s) (hj : x.InForce j s) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := x.stamp_mono (Nat.succ_le_of_lt h)
    have := hi.2; have := hj.1
    linarith
  · exact h
  · have := x.stamp_mono (Nat.succ_le_of_lt h)
    have := hj.2; have := hi.1
    linarith

/-- Every configuration up to the one in force at `s` was entered before `s` (the bare
    framework). -/
theorem Execution.InForce.stamp_lt_of_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {x : Exec Pr} {i j : Nat} {s : ℝ}
    (hi : x.InForce i s) (hji : j ≤ i) : x.stamp j < s :=
  lt_of_le_of_lt (x.stamp_mono hji) hi.1

/-- Every configuration after the one in force at `s` is entered at `s` or later (the bare
    framework). -/
theorem Execution.InForce.le_stamp_of_lt {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} {x : Exec Pr} {i j : Nat} {s : ℝ}
    (hi : x.InForce i s) (hij : i < j) : s ≤ x.stamp j :=
  hi.2.trans (x.stamp_mono (Nat.succ_le_of_lt hij))

/-- At every real time `s`, the configuration in force at `s` exists, or `s ≤ 0` and the run's
    first configuration is the one the run starts in (the bare framework). -/
theorem Execution.exists_inForce_or_start {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (s : ℝ) :
    ∃ i : Nat, x.InForce i s ∨ (i = 0 ∧ s ≤ 0) := by
  by_cases hs : s ≤ 0
  · exact ⟨0, Or.inr ⟨rfl, hs⟩⟩
  · obtain ⟨i, hi⟩ := x.exists_inForce (lt_of_not_ge hs)
    exact ⟨i, Or.inl hi⟩

/-! ### Clocks along an execution -/

/-- A corrupted validator has no clock: in every configuration of an execution, a validator in the
    corrupted set has its clock absent (the bare framework). -/
theorem Execution.clock_eq_none_of_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) (v : Node) :
    v ∈ x[i].adv → x[i].clock v = none := by
  induction i with
  | zero => intro _; exact x.init.2.1 v
  | succ i ih => exact (x.step_at i).clock_eq_none_of_mem_adv ih

/-- A corrupted validator's local state is unknown: in every configuration of an execution, a
    validator in the corrupted set has its local state `none` (the bare framework). -/
theorem Execution.getElem_eq_none_of_mem_adv {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (i : Nat) (v : Node) :
    v ∈ x[i].adv → x[i][v] = none := by
  induction i with
  | zero => intro _; exact x.init.1 v
  | succ i ih => exact (x.step_at i).getElem_eq_none_of_mem_adv ih

/-- A validator whose local state is known has a clock: in every configuration of an execution,
    `x[i][v] ≠ none` implies `x[i].clock v ≠ none` (the bare framework). -/
theorem Execution.clock_ne_none_of_getElem_ne_none {Node Msg NodeState Ev : Type}
    [DecidableEq Node] [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr)
    (i : Nat) (v : Node) : x[i][v] ≠ none → x[i].clock v ≠ none := by
  induction i with
  | zero => intro hv; exact absurd (x.init.1 v) hv
  | succ i ih => exact (x.step_at i).clock_ne_none_of_getElem_ne_none ih

/-- A clock never goes back along an execution: when `v`'s clock reads `t` after `i` steps and `t'`
    after `j ≥ i` steps, `t ≤ t'`. No hypothesis on corruption is needed, since a corrupted
    validator has no clock and never gets one again (the bare framework). -/
theorem Execution.clock_le_of_le {Node Msg NodeState Ev : Type} [DecidableEq Node]
    [DecidableEq Msg] {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} {v : Node}
    {t t' : Time} (hi : x[i].clock v = some t) (hj : x[j].clock v = some t') (hij : i ≤ j) :
    t ≤ t' := by
  -- along the steps from `i`, a reading of `v`'s clock is at least `t`, and an absent clock
  -- belongs to a corrupted `v`
  have key : ∀ j : Nat, i ≤ j →
      (∀ t'' : Time, x[j].clock v = some t'' → t ≤ t'') ∧ (x[j].clock v = none → v ∈ x[j].adv) := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base =>
        refine ⟨fun t'' h => ?_, fun h => ?_⟩
        · rw [hi] at h; exact le_of_eq (Option.some_injective _ h)
        · rw [hi] at h; exact absurd h (by simp)
    | succ j _ ih =>
        have hs := x.step_at j
        refine ⟨fun t'' h => ?_, fun h => ?_⟩
        · cases hc : x[j].clock v with
          | none =>
              have hadv := hs.adv_subset (ih.2 hc)
              rw [x.clock_eq_none_of_mem_adv (j + 1) v hadv] at h
              exact absurd h (by simp)
          | some t₀ => exact (ih.1 t₀ hc).trans (hs.clock_le hc h)
        · cases hc : x[j].clock v with
          | none => exact hs.adv_subset (ih.2 hc)
          | some t₀ => exact hs.mem_adv_of_clock_eq_none (by rw [hc]; simp) h
  exact (key j hij).1 t' hj

set_option linter.unusedVariables false in
/-- A clock never goes back along an execution: for `i ≤ j`, when `v`'s clock reads `t` after `i`
    steps and `t'` after `j` steps, and `v` is not corrupted after `j` steps, `t ≤ t'` (the bare
    framework). -/
theorem Execution.clock_mono {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) {i j : Nat} {v : Node} {t t' : Time}
    (hi : x[i].clock v = some t) (hj : x[j].clock v = some t') (hij : i ≤ j)
    (hv : v ∉ x[j].adv) : t ≤ t' :=
  x.clock_le_of_le hi hj hij

end Framework.RealStsMulticastMultisetLog

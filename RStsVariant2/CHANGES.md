# `RStsVariant2`: what changed against `RStsVariant`

Written 29 Oct 2026 (Sydney) by the lane `L20261028T1250Z-rstsvariant2` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2.md` (commit `650afe543`). Definitions only: no lemma, no proof plan.
`RStsVariant` (`experiments/r-sts-variant/`) is not edited.

## Summary

- **The clock advances by its own environment step.** `setClock p t` sets `p`'s clock to `t`. It runs no protocol code.
  It is enabled when `c[p].clock < t`, whatever `p`'s status (up, crashed, corrupted), so the clock runs while the node is
  crashed.
- **Every other node event reads the stored clock and changes none.** `tick p` (the timer interrupt) and `restart p keep`
  lose their reading argument. `tick p` is enabled when `p` is up and honest. `restart p keep` hands `Protocol.restart`
  the reading `c[p].clock`.
- **The conditions on clocks read `setClock` steps.** `TickWithinSkewR` becomes `ClockWithinSkewR`, with its two instances
  renamed to match. `DiligentWithinR` now asks for two things: each clock is set to each positive reading inside the
  window, and a node that is up and honest at that change ticks at that reading by the end of the window.
- **`RestartNotBack` is removed.** No step sets a clock back.
- **Two new conditions state two facts of real time.** `NodeStepsAtIncreasingTimesR`: each node's own steps are at
  strictly increasing real times. `PositiveDeliveryDelayR`: every delivery is strictly later than the sending.
- **29 Oct: a validator's `Local` may be unknown, and its clock left `Local`.** See the section "Unknown `Local`, 29 Oct"
  at the end of this file, with its points P9 to P16.
- **29 Oct: a restart needs the clock.** `restart p keep` is enabled only when `p`'s clock exists, `setClock` may start a
  clock before its validator comes online, and `DiligentWithinR` asks every clock to start by the real time
  `ΔClockBehind`. See the section "A restart needs the clock, 29 Oct", with its points P17 to P19.
- **29 Oct: a clock's first reading may be any reading (D-RSV2-17 (b)).** `DiligentWithinR` asks only the readings
  greater than a clock's first reading, and no longer asks a clock to start (D-RSV2-22). See the section
  "D-RSV2-17 (b), 29 Oct".
- **29 Oct: nothing is kept for a corrupted validator (D-RSV2-2 (b), D-RSV2-12 (b)).** In the bare framework, `corrupt p`
  empties `p`'s clock as well as its local state, and `setClock p t` is not enabled at a corrupted validator. In the
  condition on executions `DiligentWithinR`, a corruption by the end of a reading's window releases the validator from
  that reading (P20). See the section "D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct".
- **29 Oct: `DiligentWithinR` split into a clock condition and a tick condition (D-RSV2-6 (b)).** `ClockAdvancesWithinR`
  reads a node's clock only while the node is neither crashed nor corrupted, and a crash or a corruption by the end of a
  reading's window releases that reading (P21, which replaces P20); `TicksWithinR` is the landed tick part, stated alone;
  `DiligentWithinR` is their conjunction. See the section "D-RSV2-6 (b), 29 Oct", with its points P21 to P23.
- **29 Oct: the view leaves `Local`, and deliveries reach corrupted validators.** In the bare framework the view is a
  configuration field, `Config.view`, so every validator has one in every configuration; `deliver p e` at a corrupted
  `p` files the message into its view and runs no protocol code (`deliverSpec`). `NodeStepsAtIncreasingTimesR` counts
  honest steps only. See the section "The view leaves `Local`, 29 Oct", with its points P24 to P28.
- **29 Oct: unused definitions removed (D-RSV2-26 (a)).** `Safe`, `Live`, `Secure`, `DeliverFair`, `CustomFair`,
  `CorruptionBounded`, `Execution.Up`, and the lemmas `nodes_apply`, `Config.setNode_apply`, `Addressed.addressed_sign`.
  See the section "D-RSV2-26 (a), 29 Oct", with its point P29.
- **29 Oct: the network's condition split three ways, over deadline functions (D-ADQ3 (d), D-TSV7 (b), D-RTS2 (a)).**
  `DeliveredBeforeActing dl` (fresh deliveries), `CatchUpAfterRestart dl dlW` (what a restarted node is owed),
  `SyncedWithinBy serves sync` (what is served reaches a node up and honest), with `syncDeadline` and `deadlineOutside`.
  See the section "D-ADQ3 (d), D-TSV7 (b), D-RTS2 (a), 29 Oct", with its points P30 and P31.
- **Points for Roberto: P1 to P8 in the section "Points for Roberto".** The two with the most effect are P1, the step relation allows
  several ticks at one reading, and P5, a node restarted while its clock reads `t` is not owed a tick at `t`.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. No `sorry`, `axiom` or `native_decide`.

## The changes, one by one

Every path is relative to `experiments/r-sts-variant-2/RStsVariant2/`. Every node event runs at the node's clock
reading, called "the stored reading" in this section.

### `Spec/Protocol.lean`

| definition | old form (`RStsVariant`) | new form | why |
| --- | --- | --- | --- |
| `Action.setClock p t` (`Spec/Protocol.lean:376`) | absent | new environment step: `p`'s clock comes to read `t` | the clock is the node's hardware: it advances by a step of its own, not by the protocol's tick (Cristian and Fetzer 1999 §III, `experiments/sts-variant/step_model_literature.md`) |
| `spec`, case `.setClock p t` (`Spec/Protocol.lean:599`) | absent | `Enabled c := c[p].clock < t`, `Effect c c' := c' = setClock p t c` | enabled whatever `p`'s status, so the clock runs while `p` is crashed; the clock strictly increases |
| `Action.tick` (`Spec/Protocol.lean:378`) | `tick (p : Node) (t : Time)`: set the clock to `t`, then run the tick reaction at `t` | `tick (p : Node)`: run the tick reaction at the stored reading | a tick is the interrupt saying the clock has reached a new reading; it no longer moves the clock |
| `NodeAction.tick` (`Spec/Protocol.lean:359`) | `tick (t : Time)` | `tick` | the same, for the reaction a `crashDuring` interrupts |
| `nodeSpec`, tick case (`Spec/Protocol.lean:572`) | `p ∉ c.adv ∧ p ∉ c.crashed ∧ c[p].clock < t` | `p ∉ c.adv ∧ p ∉ c.crashed` | the reading test now sits on `setClock` (see P1) |
| `NodeAction.prepare` (`Spec/Protocol.lean:543`) | tick case `setClock p t c` | tick case `c` | no node action changes the clock |
| `NodeAction.event` | `.tick _ => .tick` | `.tick => .tick` | the argument is gone |
| `Action.restart` (`Spec/Protocol.lean:402`) | `restart (p : Node) (t : Time) (keep : Bool)`, sets the clock to `t` | `restart (p : Node) (keep : Bool)`, the clock unchanged | the clock is hardware and kept running while `p` was crashed |
| `spec`, case `.restart p keep` (`Spec/Protocol.lean:641`) | `clock := t, st := Pr.restart t keep (…)` | `st := Pr.restart c[p].clock keep (…)` | `Protocol.restart` keeps its type `Time → Bool → NodeState → NodeState` and is handed the stored reading (P3) |
| `Action.deliver`, docstring | the reaction runs at the stored reading | unchanged, and it now says that the framework does not order a delivery and a tick at one reading, so a protocol whose reaction to a delivery must follow its reaction to the current reading runs that reaction first in its own `recv` handler | asked by the brief |
| `Event.tick`, `Local.clock`, `Config.crashed`, `Protocol.restart`, `ActionSpec`, `spec`, `nodeSpec`, `setClock` (the configuration setter): docstrings | written for a tick that set the clock | rewritten: only `setClock` changes a clock, whatever the node's status | to match the new steps |
| module docstring | "Real time is the execution's; each node ticks by itself" | "Real time is the execution's; the clock advances by a step of its own", and a new section "What differs from `RStsVariant`, and why", citing the literature file | asked by the brief |

### `Spec/Execution.lean`

| definition | old form (`RStsVariant`) | new form | why |
| --- | --- | --- | --- |
| `ClockWithinSkewR ΔClockAhead ΔClockBehind` (`Spec/Execution.lean:217`) | `TickWithinSkewR kAhead kBehind`: every `tick p t` and every `crashDuring p (.tick t) n` at a real time in `[t − kAhead, t + kBehind]` | every `setClock p t` at a real time in `[t − ΔClockAhead, t + ΔClockBehind]` | only `setClock` sets a reading now |
| `ClockNotAheadR`, `ClockAtTimeR` (`Spec/Execution.lean:227`, `:234`) | `TicksNotAheadR`, `TicksAtTimeR` | the same instances (`ΔClockAhead = 0`; both `0`), of `ClockWithinSkewR` | renamed with it |
| `RestartNotBack` | a restart with reading `t` only when the clock reads at most `t` | removed | nothing can set a clock back: `restart` leaves the clock as it is, and `setClock` only moves it forward |
| `DiligentWithinR ΔClockAhead ΔClockBehind` (`Spec/Execution.lean:361`) | every node up and honest in the configuration in force at `t − kAhead` takes `tick p t`, or is corrupted or crashes, inside `[t − kAhead, t + kBehind]` | see the statement after this table | the tick no longer moves the clock, so the condition asks for the clock change and for the tick separately |
| `Action.RunsCodeOf p` (`Spec/Execution.lean:250`) | absent | the step runs code of `p`: `tick p`, `deliver p e`, `custom p ev`, `crashDuring p na n`, `restart p keep` | needed to state `NodeStepsAtIncreasingTimesR` |
| `NodeStepsAtIncreasingTimesR` (`Spec/Execution.lean:271`) | absent | see the statement after this table | Roberto: with real time, a node never has two events at the same real time |
| `PositiveDeliveryDelayR` (`Spec/Execution.lean:286`) | absent | see the statement after this table | Roberto: with real time, no message has zero delay |
| `DueBy` (`Spec/Execution.lean:414`) | restart clause over `.restart p t' keep` | over `.restart p keep` | the label changed; nothing else |
| `DeliveredBeforeActing` (`Spec/Execution.lean:462`) | acting steps `tick p t`, `custom p ev`, `crashDuring p (.tick t) m`, `crashDuring p (.custom ev) m`; void clause `restart p t false` | acting steps `tick p`, `custom p ev`, `crashDuring p .tick m`, `crashDuring p (.custom ev) m`; void clause `restart p false` | the labels changed; nothing else |
| `NoCrashDuring` | docstring names `restart p t false` | names `restart p false` | the label changed |
| module docstring, the "Clocks and real time" section, the "Fairness" section | written for ticks that set the clock | rewritten for `setClock`; a new section "Real time at a node's own steps"; a section "What differs from `RStsVariant`" | asked by the brief |

Not changed: `Spec/Message.lean` (namespace only), `Execution`, `InForce` (no condition of this file uses it any more;
kept), `Up`, `Honest`, `CorruptionBounded`, `WeakFair`, `StrongFair`, `DeliverFair`, `CustomFair`, `Safe`, `Live`, `Secure`,
`Init`, `Step`, `system`. D-ADQ3, D-TSV7 and D-RTS2 are not applied.

### The restated and new conditions on executions

`DiligentWithinR ΔClockAhead ΔClockBehind x`:

```lean
∀ (t : Time) (p : Node), 0 < t →
  ∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv →
      ∃ j : Nat, i < j ∧ x[j][p].clock = t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))
```

Read aloud: every node's clock comes to read each positive `t` at a real time between `t − ΔClockAhead` and
`t + ΔClockBehind`. A node that is up and honest at that change then takes its timer interrupt while its clock still
reads `t`, by the real time `t + ΔClockBehind`, unless it is first corrupted or crashed.

Every node is bound by the first half, crashed and corrupted ones included, so no clock skips a reading.

`NodeStepsAtIncreasingTimesR x`:

```lean
∀ (i j : Nat) (p : Node), i < j → (x.lbl i).RunsCodeOf p → (x.lbl j).RunsCodeOf p →
  x.stamp (i + 1) < x.stamp (j + 1)
```

Read aloud: whenever `p` takes a step at `i` and another at a later `j`, the real time of the second is strictly greater
than the real time of the first. "A step of `p`" is `tick p`, `deliver p e`, `custom p ev`, `crashDuring p na n` or
`restart p keep`.

`PositiveDeliveryDelayR x`:

```lean
∀ (j : Nat) (p : Node) (e : Envelope Node Msg),
  (x.lbl j = .deliver p e ∨ ∃ n : Nat, x.lbl j = .crashDuring p (.deliver e) n) →
  ∃ i : Nat, i < j ∧ e ∈ x[i + 1].sent - x[i].sent ∧ x.stamp (i + 1) < x.stamp (j + 1)
```

Read aloud: every delivery of an envelope `e`, completed or interrupted by a crash, comes after a step that put a copy
of `e` on the wire, at a real time strictly less than the delivery's.

## Points for Roberto

Each is a default the brief fixed or this lane chose. Each gives the alternative.

**P1. `tick p` may be taken several times at one reading.** The brief fixes the enabling condition "`p` up and honest".
So the step relation allows any number of ticks while the clock reads `t`. In `RStsVariant`, `c[p].clock < t` allowed
exactly one tick per reading between restarts, and a tick reaction did not need to be idempotent. Here a protocol whose
tick reaction must run once per reading keeps in its state the last reading it reacted to. The docstrings say so.
Alternative: a per-node field in `Local`, set by `setClock` and cleared by `tick`, so that `tick p` is enabled once per
reading. It moves the question of P5 into the step relation (does `restart` set the field?).

**P2. `setClock` is enabled for a corrupted node too.** The brief says "whatever `p`'s status". A corrupted node never
ticks, so its clock changes nothing the protocol sees. Alternative: enable it only for honest nodes. Then the first half
of `DiligentWithinR` would have to exclude corrupted nodes.

**P3. `Protocol.restart` keeps its reading argument.** Its type stays `Time → Bool → NodeState → NodeState`, and it is
called with `c[p].clock` (the brief's default). Alternative: drop the `Time` argument. Then a protocol learns the reading
only at its next tick, delivery or event.

**P4. Which steps count as `p`'s own in `NodeStepsAtIncreasingTimesR`.** The brief requires `tick`, `deliver`, `custom`,
`restart` and `crashDuring` of `p`. They are exactly the steps that run code of `p`.
- `setClock p t` is not counted. It is the node's clock, not its program. A tick taken at the real time its clock
  changed is the interrupt raised as the clock moves. If it counted, the tick would be strictly later than the change.
  Then a change taken at exactly `t + ΔClockBehind` would leave no real time for the tick that `DiligentWithinR` asks by
  `t + ΔClockBehind`, and the condition would exclude every such run, which is a choice of the environment.
- `crash p` and `corrupt p` are not counted: they run no code of `p`. Alternative: count `crash p`. Then a crash right
  after a completed step, at the same real time, is excluded; `crashDuring` still covers a crash during a reaction.
- `adversarial p m recipients` is not counted: it is the adversary's send, not `p`'s program.

**P5. A node restarted while its clock reads `t` is not owed a tick at `t`.** `DiligentWithinR` binds a node that is up
and honest when its clock comes to read `t`. A node crashed at that moment and restarted while its clock reads `t` is
not bound. It may tick at `t` (`tick p` is enabled once it is up), but it is not asked to. The reason is that its restart
may come at any real time before its clock's next change, as late as `t + 1 + ΔClockBehind`. So no deadline inside the
window of `t` fits it. `RStsVariant`'s `DiligentWithinR` did not ask it either ("A node restarted after `t − kAhead` is
not asked to tick to `t`"). Alternative: ask the restarted node to tick before its clock's next change, unless it is
corrupted or crashes first. Under `NodeStepsAtIncreasingTimesR` that tick is strictly later than the restart. So the
condition would exclude every run in which the restart and the next clock change share a real time with the restart
first in the sequence. That fixes an order between two steps at one real time, which D-ORD1 (b) avoids for a delivery
and a tick.

**P6. Every clock visits every positive reading.** The first half of `DiligentWithinR` asks `setClock p t` for every node
and every `t > 0`, inside the window, whatever the node's status. With clocks that only move forward, each clock then
reads each positive reading exactly once. `RStsVariant` forced a reading only on nodes up and honest at `t − kAhead`, and
let a crashed node's clock jump. Alternatives: (a) split the clock half into a condition of its own, so that a statement
can take it without the tick half; (b) bind it only for nodes up at the change, which would let a crashed node's clock
skip readings, against the clock running while crashed.

**P7. Where "up and honest" is read.** `DiligentWithinR` reads it in the configuration `x[i]` from which `setClock p t`
is taken. `setClock` changes neither `crashed` nor `adv`, so `x[i]` and `x[i + 1]` agree. `RStsVariant` read it in the
configuration in force at `t − kAhead`. Alternative: keep that reading, which binds a node up at `t − ΔClockAhead` even
if it crashes before its clock changes; the crash disjunct then discharges it.

**P8. `PositiveDeliveryDelayR` asks for one copy sent strictly earlier.** The sent log keeps every copy, and a delivery
does not name its copy, so "strictly later than the sending" is read as "strictly later than the first sending". It
counts an interrupted delivery (`crashDuring p (.deliver e) n`) too, since that files the message into the view.
Alternative: count completed deliveries only.

## Taken, tell me to revisit

- **T1. Names.** `ClockWithinSkewR`, `ClockNotAheadR`, `ClockAtTimeR` (singular "Clock", by what each says),
  `Action.RunsCodeOf`, `NodeStepsAtIncreasingTimesR`, `PositiveDeliveryDelayR`. The configuration setter keeps its name
  `setClock`, beside the constructor `Action.setClock`.
- **T2. Variable names.** The clock bounds of the definitions rewritten here are `ΔClockAhead` and `ΔClockBehind`
  (the naming conventions of 28 Oct). Unchanged definitions keep their names: `gst`, `delta`, `deltaW` in `DueBy` and
  `DeliveredBeforeActing`, and `p` for a node throughout (D-NAM4: no sweep). New step indices are `i`, `j`.
- **T3. Copied docstrings left as they were.** Only the lines this lane wrote were checked against the word table: the
  unchanged text keeps "record", "below", "above", and "pool" (Majorum's transaction pool).
- **T4. Placement.** `Action.RunsCodeOf` and the two new conditions sit in `Spec/Execution.lean`, in a new section "Real
  time at a node's own steps", after the clock conditions.
- **T5. The edit scripts** (`scratch/rsts2/scripts/edit_protocol.py`, `edit_execution.py`, `edit_root.py`, in the
  worktree `scratch/worktrees/rsts2`) are not committed, so the branch's diff stays within the three paths the brief
  names.

## Unknown `Local`, 29 Oct

**AMENDED BY the section "A restart needs the clock, 29 Oct" (Roberto's ruling between 01:10 and 01:16 AEDT): a restart
needs the clock, and `setClock` may start a clock before its validator comes online. That settles P9, P11 (its
alternative (a)), P15 and P16 of this section; the rows on `spec`'s `setClock` and `restart` cases and on
`DiligentWithinR` in the table of this section describe the state before that change.**

Written 29 Oct 2026 (Sydney) by the lane `rsts2c` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_unknown_local.md`. Definitions only.

Roberto's rulings of 29 Oct, which this section renders:

1. A validator's `Local` is unknown before it first comes online and after it is corrupted; a crashed validator keeps
   its `Local`.
2. Every validator starts with an unknown `Local`; `restart p keep` acting on an unknown `Local` brings the validator
   online, building its state from the protocol's initial state.
3. A validator's clock does not exist before it first comes online.

### Summary

- `Config.nodes : Node → Option (Local Node Msg NodeState)`: `none` is an unknown local state. `c[p]` now reads the
  `Option`.
- The clock left `Local` for a configuration field of its own, `Config.clock : Node → Option Time`, `none` before the
  validator's clock exists.
- `Init`: every validator's local state `none`, every clock `none`, nothing sent.
- `restart p keep` at a validator whose local state is unknown gives it `Pr.initialLocal p` (its initial state in
  memory, `Pr.persist` of it on disk, an empty view), whatever `keep`.
- `corrupt p` sets `p`'s local state to `none`; its clock is left as it is.
- `tick`, `deliver`, `custom` and `crashDuring` need the local state known and the clock existing, besides up and
  honest.
- The clock is started by the first `setClock p t` after `p` came online (P9).

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. No `sorry`, `axiom`, `native_decide` or `variable`.

### The changes, one by one

Every path is relative to `experiments/r-sts-variant-2/RStsVariant2/`.

| definition | before | now |
| --- | --- | --- |
| `Local` (`Spec/Protocol.lean:317`) | fields `clock`, `st`, `disk`, `view` | fields `st`, `disk`, `view`: the clock is no longer in it |
| `Protocol.initialLocal` (`Spec/Protocol.lean:332`) | absent | `{ st := Pr.init p, disk := Pr.persist (Pr.init p), view := ∅ }`: the local state a validator is given when it comes online |
| `Config.nodes` (`Spec/Protocol.lean:351`) | `Node → Local …` | `Node → Option (Local …)` |
| `Config.clock` (`Spec/Protocol.lean:360`) | absent (it was `Local.clock : Time`) | `Node → Option Time` |
| `Config.adv`, `Config.crashed`: docstrings | | a corrupted validator's local state is unknown and no restart gives it one; "down" is defined (P10) |
| `c[p]` (`Spec/Protocol.lean:394`) | `Local …` | `Option (Local …)` |
| `Config.setNode`, `Config.setNode_apply` (`Spec/Protocol.lean:474`, `:481`) | take a `Local` | take an `Option Local` |
| `receive`, `applyEffect` (write), `applyNodeStepResult` (`Spec/Protocol.lean:497`, `:504`, `:524`) | `{ c[p] with … }` | `c[p].map fun l => { l with … }`: they change nothing when the local state is unknown, a case no step reaches |
| `setClock`, the configuration setter (`Spec/Protocol.lean:542`) | set `c[p].clock := t` | set `Config.clock` at `p` to `some t` |
| `NodeStep`, `CrashDuringStep` (`Spec/Protocol.lean:555`, `:566`) | `∃ res, Pr.step p pre[p].clock pre[p].st e res ∧ …` | `∃ l t res, pre[p] = some l ∧ pre.clock p = some t ∧ Pr.step p t l.st e res ∧ …` |
| `nodeStep_total` (`Spec/Protocol.lean:575`) | for every configuration | takes `pre[p] = some l` and `pre.clock p = some t` |
| `nodeSpec` (`Spec/Protocol.lean:660`) | per case: `p ∉ c.adv ∧ p ∉ c.crashed` (and the case's own condition) | `p ∉ c.adv ∧ p ∉ c.crashed ∧ ∃ l t, c[p] = some l ∧ c.clock p = some t ∧` the case's own condition; `custom` reads `Pr.enabled t l.st ev`. Its `feasible` now proves in place that a delivery's starting configuration keeps the local state known |
| `spec`, `.setClock p t` (`Spec/Protocol.lean:701`) | `c[p].clock < t` | `match c.clock p with \| some r => r < t \| none => c[p] ≠ none` |
| `spec`, `.corrupt p` (`Spec/Protocol.lean:715`) | `c' = { c with adv := insert p c.adv }` | `c' = { c.setNode p none with adv := insert p c.adv }` |
| `spec`, `.crash p` (`Spec/Protocol.lean:724`) | | unchanged condition and effect; comment says a validator that has never come online may crash (P14) |
| `spec`, `.crashDuring p a k` (`Spec/Protocol.lean:734`) | | the same change of condition as `nodeSpec`; `feasible` reproved |
| `spec`, `.restart p keep` (`Spec/Protocol.lean:761`) | enabled `p ∈ c.crashed`; state `Pr.restart c[p].clock keep (…)` | enabled `p ∉ c.adv ∧ (p ∈ c.crashed ∨ c[p] = none)`; local state `{ l with st := Pr.restart t keep (…) }` when `c[p] = some l` and `c.clock p = some t`, `Pr.initialLocal p` otherwise (P11, P13) |
| `Init` (`Spec/Protocol.lean:803`) | `Init Pr c`: every `c[p]` at clock `0` in its initial state | `Init c`: `(∀ p, c[p] = none) ∧ (∀ p, c.clock p = none) ∧ c.sent = 0`; the protocol is no parameter any more (T7) |
| `Action.setClock`, `Action.corrupt`, `Action.restart` (`Spec/Protocol.lean:431`, `:445`, `:460`): docstrings | | rewritten for the cases in the rows on `spec` |
| module docstring of `Spec/Protocol.lean` | | new section "Unknown local state" (`Spec/Protocol.lean:97`); the setClock, tick, memory and disk, crash and restart passages updated |
| `Execution.Up` (`Spec/Execution.lean:158`) | `p ∉ x[i].crashed` | `p ∉ x[i].crashed ∧ (x[i][p] ≠ none ∨ p ∈ x[i].adv)` (P10) |
| `DiligentWithinR` (`Spec/Execution.lean:407`) | every node, every reading `t > 0` | binds a node only for the readings whose window has not ended when it comes online, with a case for a corruption before the clock was started; reading `0` included (P15) |
| `ClockWithinSkewR`, `DueBy`, `DeliveredBeforeActing` (`Spec/Execution.lean:238`, `:467`, `:518`): docstrings | | a clock's first reading is set by `setClock` too; the restart that brings a validator online counts as a restart for the catch-up deadline |
| `Spec/Message.lean`, `RStsVariant2.lean`, `Spec/Execution.lean` module docstrings | `Local.clock` | `Config.clock p`; a note on the 29 Oct change |

Not changed in their Lean text (some docstrings are, as the table says): `Action`'s constructors and their arguments, `Protocol` (its fields and types), `Execution`, `InForce`,
`Honest`, `CorruptionBounded`, `NoCrashDuring`, `ClockWithinSkewR`, `NodeStepsAtIncreasingTimesR`,
`PositiveDeliveryDelayR`, the fairness conditions, `DueBy`, `DeliveredBeforeActing`, `Safe`, `Live`, `Secure`, `Step`.

### `DiligentWithinR`, restated

```lean
∀ (t : Time) (p : Node) (i₀ : Nat), x[i₀][p] ≠ none → x.stamp i₀ ≤ t + ΔClockBehind →
  (∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))) ∨
  (∃ k : Nat, x.lbl k = .corrupt p ∧ x[k].clock p = none ∧
    x.stamp (k + 1) ≤ t + ΔClockBehind)
```

Read aloud: take any reading `t` and any node `p` whose local state is known in some configuration entered no later
than `t + ΔClockBehind`, that is, `p` came online by the end of `t`'s window. Then either `p`'s clock comes to read `t`
between the real times `t − ΔClockAhead` and `t + ΔClockBehind`, and `p`, if up and honest at that moment, takes its
timer interrupt while its clock reads `t`, by the real time `t + ΔClockBehind`, unless it is corrupted or crashed
first; or `p` was corrupted, by the real time `t + ΔClockBehind`, while its clock did not exist.

### Points for Roberto, 29 Oct

The brief's four points are P9 to P12. P13 to P16 are choices this lane had to make to land the rulings. Each gives
the default landed and the alternative.

**P9. How a validator's clock starts when it first comes online.** Default: the first `restart` gives the validator
its local state and no clock; the clock stays `none` until a `setClock p t`, enabled when `p`'s clock is `none` and its
local state is known, starts it at any reading `t`. Until then the validator takes no step that runs its reaction: a
reaction runs at a reading, so `tick`, `deliver`, `custom` and `crashDuring` need the clock to exist. Which reading the
clock starts at is a condition on executions: `ClockWithinSkewR` puts that `setClock` in `t`'s window, and
`DiligentWithinR` asks for every reading whose window has not ended when the validator comes online (P15).
Alternative: the first `restart` carries the starting reading. `Action.restart` would take a reading used only when
the local state is unknown, or a separate action `start p t` would do the first restart; either way no validator is
ever online without a clock, and P11 does not arise.

**P10. Whether a validator that has never come online is in `crashed`.** (D-RSV2-10. It no longer arises since
`Execution.Up` was removed: see the section "D-RSV2-26 (a), 29 Oct".) Default: it is not. "Down" is read as "in
`crashed`, or local state unknown and not corrupted", and `Execution.Up i p` is
`p ∉ x[i].crashed ∧ (x[i][p] ≠ none ∨ p ∈ x[i].adv)`. So an honest validator is up exactly when it is outside
`crashed` with its local state known, and a corrupted validator outside `crashed` is up, as before. `Live` therefore
asks nothing of an honest validator that has not come online. Alternatives: (a) put every validator in `crashed` at
the start, `Init` saying `∀ p, p ∈ c.crashed`. With `crashed : Finset Node` that needs `Node` finite (a `Fintype`
instance), or `crashed` turned into a `Set`; restart is then enabled by membership in `crashed` alone. (b) Keep the
default for honest validators, but make a corrupted validator never up (`Up` would be
`p ∉ x[i].crashed ∧ x[i][p] ≠ none`).

**P11. What `Protocol.restart`'s reading argument receives at a restart while the clock is still `none`.** Default:
`Protocol.restart` is not called. That restart happens only to a validator that came online and crashed before its
clock was started. Every reaction needs a reading, so such a validator has run none since it came online, and its
local state is still `Pr.initialLocal p`. The restart gives it `Pr.initialLocal p` again, whatever `keep`, and takes it
out of `crashed`. Alternatives: (a) `restart` is not enabled while the clock is `none`; the validator then waits,
crashed, for the `setClock` that starts its clock (enabled, since its local state is known), and `Protocol.restart`
always gets a reading. (b) `Protocol.restart` takes an `Option Time`, and each protocol says what it does without a
reading.

**P12. Whether a corrupted validator's clock goes on existing.** Default: yes. `corrupt p` leaves `Config.clock` as it
is, `setClock` stays enabled whatever the status once the clock exists, and `DiligentWithinR` keeps asking a corrupted
validator's clock for every reading. The clock is the hardware, and nothing reads a corrupted validator's clock.
Alternative: `corrupt p` also sets the clock to `none`. Then `setClock p t` is never enabled after the corruption, and
`DiligentWithinR` must release a corrupted node from the clock half, as it already does for a node corrupted before its
clock was started.

**P13. `restart` is not enabled at a corrupted validator.** Before, `restart p keep` was enabled at any validator in
`crashed`, corrupted or not. A restart now brings a validator whose local state is unknown online, and a corrupted
validator's local state is unknown, so a restart of one would hand the adversary's validator a known honest state.
Default: `restart p keep` is enabled when `p ∉ c.adv` and (`p ∈ c.crashed` or `c[p] = none`). Alternative: enable it at
a corrupted validator in `crashed` too, taking it out of `crashed` and leaving its local state `none`; this changes
nothing the adversary can do, since `adversarial` does not read `crashed`.

**P14. `crash` stays enabled at a validator that has never come online.** Its condition is unchanged, `p ∉ c.crashed`.
Such a crash puts `p` in `crashed` with its local state unknown; `p` is down either way, and its `restart` brings it
online as it would without the crash. Alternative: `crash p` needs `c[p] ≠ none`, so that only a validator that has come
online can crash.

**P15. Which readings `DiligentWithinR` asks of a node.** Default: a node is bound for a reading `t` once its local
state is known in a configuration entered no later than `t + ΔClockBehind`. So a node that comes online at the real
time `s` must have its clock read every `t` with `t + ΔClockBehind ≥ s`, each inside `t`'s window, and none earlier: its
clock did not exist then. Two cases are new. A node corrupted while its clock did not exist yet never gets one
(`setClock` starts a clock only at a known local state), so the condition then holds by a corruption at a real time at
most `t + ΔClockBehind`. And the reading `0` is now asked like any other, since no clock reads `0` at the start (the old
`0 < t` is dropped). The tick half is unchanged. Alternatives: (a) state the start of the clock as a condition of its
own, with its own deadline after the restart that brings the node online, and keep the reading half for nodes whose
clock exists; (b) bind a node only from the reading after the one its clock starts at, leaving the start to
`ClockWithinSkewR` alone. Under (b) a node may come online and leave its clock unstarted forever.

**P16. A validator online with no clock is up and does nothing.** Between the restart that brings it online and the
`setClock` that starts its clock, `Execution.Up` holds of it (P10), but it takes no tick, no delivery and no event (P9).
`DeliveredBeforeActing` owes it nothing, since it takes no acting step; `Live` asks of it what it asks of any up,
honest validator. Alternative: read "up" as needing the clock to exist too,
`p ∉ x[i].crashed ∧ (x[i][p] ≠ none ∧ x[i].clock p ≠ none ∨ p ∈ x[i].adv)`.

### Taken, tell me to revisit

- **T6. Names.** `Config.clock` (the brief's example), `Protocol.initialLocal` for the local state a validator comes
  online with. The configuration setter keeps its name `setClock`.
- **T7. `Init` takes no protocol.** With every local state unknown, `Init` no longer reads `Pr`, and the parameter drew
  the unused-variable warning. It is `Init c` now, and `system` says `Init := Init`.
- **T8. `c[p]` is the `Option`.** Indexing a configuration returns `Option (Local …)`, so every reader matches on it or
  states `c[p] = some l`. The writes to a part of the local state (`receive`, the `write` effect, the final write of
  `applyNodeStepResult`) are `Option.map`: a no-op on an unknown local state, a case no step reaches.
- **T9. `nodeSpec`'s condition has one shape for the three node actions**: `p ∉ c.adv ∧ p ∉ c.crashed ∧ ∃ l t,
  c[p] = some l ∧ c.clock p = some t ∧` the action's own condition. Its `feasible`, and `crashDuring`'s, are short
  tactic proofs in place (`cases` on the node action, `simp` on `receive`); `nodeStep_total` takes the two equations.
- **T10. The edit blocks and the splice script** are committed in `scratch/rsts2c/edits/`, the ledger and the checks in
  `scratch/rsts2c/`.

## A restart needs the clock, 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2e` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_restart_needs_clock.md`. Definitions only.

Roberto's ruling (29 Oct, between 01:10 and 01:16 AEDT): "I think that the restart enable condition is tha tthe clock is
not empty", then "yes" to the coordinator's proposal:

1. `Config.clock` stays `Node → Option Time` (the earlier "cannot be optional" is withdrawn);
2. `restart p keep` is enabled only when `Config.clock p` is not `none`, in addition to its condition before;
3. `setClock p t` with an absent clock is enabled whatever `p`'s `Local`, so a clock can start before the validator
   first comes online;
4. `Init` is unchanged: every clock `none`, every `Local` unknown;
5. `DiligentWithinR` says every validator's clock starts by the real time `ΔClockBehind` and then comes to every reading
   within the skew bounds.

### Summary

- `setClock p t` at a validator whose clock does not exist is enabled whatever `p`'s status: local state unknown (not
  yet online, or corrupted) or known.
- `restart p keep` is enabled when `p ∉ c.adv ∧ (p ∈ c.crashed ∨ c[p] = none) ∧ c.clock p ≠ none`. Its effect always
  has a reading `t`: `Pr.initialLocal p` at an unknown local state, `Pr.restart t keep …` at a known one. The case
  "local state known, no clock" is gone: it cannot happen any more.
- So a validator's clock starts before it first comes online, a validator whose local state is known always has a
  clock, and `Protocol.restart` is always handed a reading.
- `DiligentWithinR` asks every node, whatever its status, for every reading `t`, the reading `0` included, a
  `setClock p t` in `t`'s window; the reading `0` is therefore the clock's start, at a real time at most `ΔClockBehind`.
  The tick part is as before, asked of a node up and honest when its clock comes to read `t`.
- `Init` is unchanged in its Lean text; its docstring says the clock starts before the first restart.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. No `sorry`, `axiom`, `native_decide` or `variable`.

### The changes, one by one

Every path is relative to `experiments/r-sts-variant-2/RStsVariant2/`.

| definition | before | now |
| --- | --- | --- |
| `spec`, `.setClock p t` (`Spec/Protocol.lean:713`) | `match c.clock p with \| some r => r < t \| none => c[p] ≠ none` | `match c.clock p with \| some r => r < t \| none => True` |
| `spec`, `.restart p keep` (`Spec/Protocol.lean:771`): condition | `p ∉ c.adv ∧ (p ∈ c.crashed ∨ c[p] = none)` | `p ∉ c.adv ∧ (p ∈ c.crashed ∨ c[p] = none) ∧ c.clock p ≠ none` |
| `spec`, `.restart p keep`: effect | `c' = { c.setNode p (some (match c[p], c.clock p with \| some l, some t => … \| _, _ => Pr.initialLocal p)) with … }` | `∃ t, c.clock p = some t ∧ c' = { c.setNode p (some (match c[p] with \| some l => { l with st := Pr.restart t keep (…) } \| none => Pr.initialLocal p)) with … }`; `feasible` now takes `t` from the condition (`Option.ne_none_iff_exists'`) |
| `DiligentWithinR` (`Spec/Execution.lean:406`) | `∀ t p i₀, x[i₀][p] ≠ none → x.stamp i₀ ≤ t + ΔClockBehind → (∃ i, setClock p t in the window ∧ tick part) ∨ (∃ k, corrupt p at k while the clock is none, by t + ΔClockBehind)` | `∀ t p, ∃ i, setClock p t in the window ∧ tick part`, the tick part asked when `p ∉ x[i].crashed`, `p ∉ x[i].adv` and `x[i][p] ≠ none` (P19) |
| `Protocol.restart`, `Config.clock`, `Action.setClock`, `Action.restart`, `nodeSpec`, `spec`, `Init` (`Spec/Protocol.lean:317`, `:369`, `:441`, `:470`, `:671`, `:713`, `:816`): docstrings and comments | | the clock may start before the validator comes online; a restart needs it; the case "known local state, no clock" removed |
| module docstring of `Spec/Protocol.lean` | | the `setClock` and `restart` bullets (`Spec/Protocol.lean:46`), a paragraph on this change (`:78`), the section "Unknown local state" (`:103`) and the section "Crash and restart" (`:171`) |
| module docstrings of `Spec/Execution.lean` and `RStsVariant2.lean`, the section "Clocks and real time" | | the clock starts before the first restart; `DiligentWithinR` asks it to start by `ΔClockBehind` |

Not changed: every other definition, `Init`'s Lean text, `Execution.Up`, `ClockWithinSkewR`, `nodeSpec`'s condition (it
still names the reading `t` with `c.clock p = some t`; that conjunct now follows from `c[p] = some l` in every
configuration a run reaches, see "What this settles", but it is what hands the reaction its reading).

### `DiligentWithinR`, restated

```lean
∀ (t : Time) (p : Node),
  ∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))
```

Read aloud: for every reading `t` and every node `p`, whatever its status, `p`'s clock comes to read `t` between the real
times `t − ΔClockAhead` and `t + ΔClockBehind`; and `p`, if up and honest at that moment (outside `crashed`, outside
`adv`, its local state known), then takes its timer interrupt at the reading `t` by the real time `t + ΔClockBehind`,
unless it is corrupted or crashed first. For `t = 0` this says that every node's clock starts, at the reading `0`, by
the real time `ΔClockBehind`.

Why the reading `0` is the start: no clock exists at the start, and a clock only moves forward, so the `setClock p 0`
the condition asks for is the step that starts `p`'s clock, at a real time in `[0, ΔClockBehind]`. From the
configuration after it on, `p`'s clock exists: in every configuration entered after the real time `ΔClockBehind`, and
in every configuration in force at a real time after `ΔClockBehind` (P18 says what happens at exactly `ΔClockBehind`).

### What this settles

These are the points of the section "Unknown `Local`, 29 Oct", posed as D-RSV2-9 to D-RSV2-16 in
`experiments/goldilocks/OPEN_DECISIONS.md` (not edited by this lane).

- **D-RSV2-9 (P9, how the clock starts): settled.** The clock starts by a `setClock`, which may come before the
  validator comes online and must come before its first restart. Neither the old default (the clock started after the
  validator came online) nor the old alternative (the first restart carries the starting reading).
- **D-RSV2-11 (P11, `Protocol.restart` without a reading): option (b),** P11's alternative (a): `restart` is not enabled
  while the clock is `none`, and `Protocol.restart` always gets a reading.
- **D-RSV2-15 (P15, which readings `DiligentWithinR` asks): settled** as ruled: every node, every reading, `0` included,
  whatever the node's status; the clock starts by `ΔClockBehind`. The binding "once the node has come online" and the
  case "corrupted before its clock was started" are gone: `setClock` is now enabled at such a node.
- **D-RSV2-16 (P16, online without a clock): cannot happen.** A validator's local state becomes known only by a
  `restart` (`Init` has every local state unknown, `corrupt` sets it unknown, and no other step sets it known), a
  `restart` needs the clock, and no step makes a clock absent again. So in every configuration a run reaches, a known
  local state comes with a clock. This is read off the step relation; no proof is written (definitions only).
- **Still open, unchanged in their text:** D-RSV2-10 (P10, a validator never online is not in `crashed`), D-RSV2-12
  (P12, a corrupted validator's clock goes on existing), D-RSV2-13 (P13, no restart of a corrupted validator), D-RSV2-14
  (P14, `crash` enabled before coming online). One effect on D-RSV2-12: a corrupted validator whose clock did not exist
  can now have it started by `setClock`, and `DiligentWithinR` asks that of it as of every node.

### Points for Roberto, the new defaults

**P17. Every clock starts at the reading `0`.** Default: `DiligentWithinR` asks every reading, `0` included, so every
clock's first reading is `0`, set at a real time in `[0, ΔClockBehind]`. This loses no run whose clocks keep within the
skew: a clock that runs ahead and should read `t₀ > 0` at a real time `s ≤ ΔClockBehind` sets `0`, `1`, …, `t₀` one
after another at the real time `s`, each inside its window, since steps may share a real time. Pros: one clause, the
same for every reading; no reading of any clock is skipped. Cons: the run carries those extra `setClock` steps.
Alternative: the clock starts at any reading `t₀`, at a real time at most `ΔClockBehind` and inside `t₀`'s window, and
`DiligentWithinR` asks only the readings greater than `t₀`. Pros: no extra steps for a clock running ahead. Cons: a
second clause (the start) beside the reading clause, and the readings less than `t₀` are never set, so a property that
counts readings from `0` must handle a clock that skipped them.

**P18. "The clock exists from `ΔClockBehind` on" is read as "after `ΔClockBehind`".** Default: nothing beyond P17 is
asked, so `p`'s clock exists in every configuration entered after the real time `ΔClockBehind`. A configuration entered
at exactly `ΔClockBehind` may come before the `setClock p 0` taken at `ΔClockBehind`, since steps at one real time come
in any order. Pros: no order is imposed on steps at one real time, as everywhere else in the conditions (D-ORD1 (b)).
Cons: the clock is not asked to exist in every configuration entered at exactly `ΔClockBehind`. Alternative: add the
clause `∀ i, ΔClockBehind ≤ x.stamp i → x[i].clock p ≠ none`. Pros: the brief's words "at or after" hold literally.
Cons: it orders the starting `setClock` before every other step at the real time `ΔClockBehind`.

**P19. The tick part asks a tick only of a node that has come online.** Default: the tick part's premise is
`p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →`, that is, `p` up and honest in configuration `i`. Before this
change the premise had no `x[i][p] ≠ none`, because `setClock` was enabled at a clock that did not exist only once the
local state was known. Now a clock may read `t` before its validator comes online; without the premise, an honest
validator not yet online would be asked, at every reading, for a tick (so it would have to come online first) or a
crash by `t + ΔClockBehind`, which forces every honest validator online, or crashed, by the end of the first window.
Pros: the condition asks a tick only where `tick p` can be enabled, as the landed docstring said ("up and honest").
Cons: none found. Alternative: the same premise spelt `x.Up i p → x.Honest i p →` (equivalent, `Execution.Up` and
`Execution.Honest`); or no premise on the local state, with the consequence just said.

### Taken, tell me to revisit

- **T11. The restart's effect is `∃ t, c.clock p = some t ∧ c' = …`**, a reading taken from the configuration, so the
  step stays deterministic and its effect has no case without a reading. The alternative was a total `match` on
  `c[p], c.clock p` with a case no enabled step reaches.
- **T12. The restart's condition lists the clock last**, `… ∧ c.clock p ≠ none`, written as the brief wrote it
  (`≠ none`, not `∃ t, … = some t`).
- **T13. `nodeSpec` keeps `c.clock p = some t`** in its condition: it names the reading the reaction runs at, although
  a known local state now comes with a clock.
- **T14. The edit block and the splice script** are committed in `scratch/rsts2e/edits/`, the ledger and the checks in
  `scratch/rsts2e/`.

## Conditions on executions in a page of their own, 29 Oct

Roberto, 29 Oct: "move all defs that that are not part of hte protocol in a separate file", and, of
`NodeStepsAtIncreasingTimesR` (D-RSV2-20 (a)), "Keep that condition, it is harmeless but I don't want to use it at the
moment". No definition's text, name or type changed; only their place. The line numbers in the sections before this
one are those of `Spec/Execution.lean` before the move.

### Summary

- `Spec/Execution.lean` keeps the framework's executions and their readings: `Execution`, its `GetElem` instance,
  `Execution.InForce`, `Exec`, `Execution.Up`, `Execution.Honest`, `Execution.Enabled`.
- The new page `Spec/Conditions.lean` (importing `Spec/Execution.lean`; the root `RStsVariant2.lean` imports it) holds
  every condition on executions (`CorruptionBounded`, `NoCrashDuring`, `ClockWithinSkewR`, `ClockNotAheadR`,
  `ClockAtTimeR`, `Action.RunsCodeOf`, `NodeStepsAtIncreasingTimesR`, `PositiveDeliveryDelayR`, `WeakFair`,
  `StrongFair`, `DiligentWithinR`, `DeliverFair`, `CustomFair`, `DueBy`, `DeliveredBeforeActing`) and every property of
  executions (`Safe`, `Live`, `Secure`), with their section headers and prose. Its module header says first that
  `RStsVariant2` assumes none of them.
- `Spec/Protocol.lean` and `Spec/Message.lean` hold no condition on executions: nothing moved from them.
- Text changed: `NodeStepsAtIncreasingTimesR`'s docstring gains "No statement takes it today; it is kept as a
  condition a statement may take."; the section "Reading an execution" names `x.Enabled i a`; the two module headers
  are split as below; `Spec/Protocol.lean`'s module header points to `RStsVariant2.Spec.Conditions` for the
  conditions it names.
- Checked: `#check @name` with `pp.all` prints the same type before and after for all 24 named declarations;
  `#print` with `pp.all` prints the same body for all 24 except for the name of an automatically generated proof of
  `True` (the indexing side condition), `Execution.Up._proof_1` before and `CorruptionBounded._proof_1` after, both of
  type `True`.

### Taken, tell me to revisit

- **T15. The old module header of `Spec/Execution.lean` is split by paragraph.** Kept in `Spec/Execution.lean`: the
  paragraph on why executions exist, "Real time is the execution's", the paragraph on digital clocks, and the paragraph
  "Since 29 Oct 2026" (it is about `Execution.Up`); moved to `Spec/Conditions.lean`: "Each predicate here is à la
  carte", the paragraph on crashes during a reaction (`NoCrashDuring`), the paragraph on a cut network, and "What
  differs from `RStsVariant`, and why" (it is about conditions only). The title of `Spec/Execution.lean` became
  "Executions in real time", and a paragraph says what each page holds.
- **T16. `Execution.Enabled` sits at the end of the section "Reading an execution"**; the prose of the section
  "Fairness", which explains why enabledness is read off `ActionSpec`, moved with the fairness conditions.
- **T17. `Spec/Protocol.lean`'s module header** names the conditions without the prefix `Execution.` (`DiligentWithinR`,
  `ClockWithinSkewR`, `DeliveredBeforeActing`, `NoCrashDuring`; none of them is in the namespace `Execution`) and points
  to `RStsVariant2.Spec.Conditions`. The definitions' own docstrings in `Spec/Protocol.lean` that still say
  `Execution.DueBy` (the field `Config.sent`), `RStsVariant2.Spec.Execution` (`setClock`) and `Execution.DiligentWithinR`
  (`nodeSpec`) are left as they are, since no definition's text changes in this step.

## D-RSV2-17 (b), 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2g` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_first_reading.md`. Definitions only.

Roberto's ruling, D-RSV2-17 (b) ("b"): in the condition on executions `DiligentWithinR`, a validator's first `setClock`
may give any reading `t₀`, and the condition asks only the readings after `t₀`. The bare framework (`Spec/Protocol.lean`,
`Spec/Execution.lean`) does not change: every clock starts empty (`Init`), and `setClock p t` is enabled when the clock
is empty or reads less than `t`. This is the alternative of P17 in the section "A restart needs the clock, 29 Oct",
without its bound "at a real time at most `ΔClockBehind`": whether a clock must start, and by when, is D-RSV2-22.

### Summary

- `DiligentWithinR` (`Spec/Conditions.lean:281`) gains a premise: for a node `p` and a reading `t`, it asks the
  `setClock p t` in `t`'s window (and the tick part) only when `p`'s clock reads less than `t` in some configuration.
  Since a clock only moves forward, that is when `t` is greater than the clock's first reading `t₀`.
- The first `setClock p t₀` is asked nothing by `DiligentWithinR`; `ClockWithinSkewR` still puts its real time in
  `t₀`'s window. A clock that never starts is asked nothing.
- The tick part is as landed. No tick is lost at `t₀`: a validator cannot be online when its clock starts, since a
  restart needs the clock.
- Docstring rewritten; it opens by saying that `DiligentWithinR` is a condition on executions, not part of the bare
  framework. The sentence of `Spec/Execution.lean`'s module header that described the old condition is rewritten (T18).
- No other definition changes. Every Lean text outside `DiligentWithinR` is unchanged.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. `#print axioms DiligentWithinR`:
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom`, `native_decide` or `variable`.

### `DiligentWithinR`, before and now

Before (`Spec/Conditions.lean:275` at `c398e4fd3`):

```lean
∀ (t : Time) (p : Node),
  ∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))
```

Read aloud: for every reading `t` and every node `p`, whatever its status, `p`'s clock comes to read `t` between the real
times `t − ΔClockAhead` and `t + ΔClockBehind`; and `p`, if up and honest at that moment, then takes its timer interrupt
at the reading `t` by the real time `t + ΔClockBehind`, unless it is corrupted or crashed first. For `t = 0` this says
that every node's clock starts, at the reading `0`, by the real time `ΔClockBehind`.

Now (`Spec/Conditions.lean:281`):

```lean
∀ (t : Time) (p : Node), (∃ (k : Nat) (t' : Time), x[k].clock p = some t' ∧ t' < t) →
  ∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))
```

Read aloud: this is a condition on executions, which the bare framework does not assume. For every node `p`, whatever
its status, once `p`'s clock has started at some reading `t₀`, then for every reading `t` greater than `t₀`, `p`'s clock
comes to read `t` between the real times `t − ΔClockAhead` and `t + ΔClockBehind`; and `p`, if up and honest at that
moment, then takes its timer interrupt at the reading `t` by the real time `t + ΔClockBehind`, unless it is corrupted
or crashed first. The first reading `t₀` may be any reading, and a clock that never starts is asked nothing.

Why the premise says "less than `t` in some configuration" and not "greater than the first reading": the two are the
same, since a clock only moves forward and its first reading is the least it ever has; the premise as written needs no
definition of "first reading".

### Points for Roberto

**D-RSV2-22. Whether a clock must start at all, and by when.** RULED (a), 29 Oct between 01:37 and 01:38 AEDT, "ok with
default" (from `experiments/goldilocks/OPEN_DECISIONS.md`, read by this lane, not edited).

- Default, (a): no condition on executions asks a clock to start. A validator whose clock never starts never comes
  online, since the bare framework's `restart` needs the clock. Pros: `DiligentWithinR` asks only what the ruling
  D-RSV2-17 (b) says; a validator that never comes online needs no clock; and a clock that starts late still keeps within
  the skew bounds of the real time, since `ClockWithinSkewR` puts its first reading in the window of the real time it starts at. Cons:
  a statement that needs a validator's clock to exist from some real time on must assume it, or assume something that
  implies it (the validator up and honest in some configuration, `Execution.Up` and `Execution.Honest`, implies its
  clock exists there, since its local state is then known; read off the step relation, not proved).
- Alternative, (b): every clock starts by some real time, a clause `∀ p, ∃ i, x.stamp i ≤ τ ∧ x[i].clock p ≠ none` with a
  bound `τ` (a new parameter, or `ΔClockBehind` as before this change). Pros: every node's clock exists after `τ`, so a
  property that reads every node's clock needs no further hypothesis. Cons: it asks a clock of validators that never
  come online, which the step relation does not need; and it brings back the question of the real time `τ` itself
  (P18 of the section "A restart needs the clock, 29 Oct": a configuration entered at exactly `τ` may come before the
  starting `setClock`).

**Effect on D-RSV2-18 (P18, "the clock exists from `ΔClockBehind` on" read as "after `ΔClockBehind`").** With D-RSV2-22
(a), no condition asks a clock to exist from any real time on, so P18's question no longer arises. It would come back
with D-RSV2-22 (b). This lane does not change D-RSV2-18; it reports the effect.

### Taken, tell me to revisit

- **T18. `Spec/Execution.lean`'s module header** (the paragraph "Since 29 Oct 2026") had the sentence "`DiligentWithinR`
  asks every node's clock to come to the reading `0`, and so to start, by the real time `ΔClockBehind`, whatever the
  node's status", which the change made false. It now says that `DiligentWithinR`, a condition on executions, asks
  every node's clock, once started at any reading, to come to every greater reading, and does not ask a clock to
  start. No definition of `Spec/Execution.lean` changes. The alternative was to leave the sentence for a later lane,
  since the brief named only `DiligentWithinR` and `CHANGES.md`.
- **T19. The premise is `∃ (k : Nat) (t' : Time), x[k].clock p = some t' ∧ t' < t`**, read off the configurations,
  rather than a premise naming the first `setClock` step and its reading. It says the same with fewer quantifiers, and
  needs no definition of the first step.
- **T20. The edit block and the splice script** are committed in `scratch/rsts2g/edits/`, the ledger and the checks in
  `scratch/rsts2g/`.

## D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2h` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_corrupt_empties.md`. Definitions only.

Roberto's rulings:

- D-RSV2-2 (b), 29 Oct between 01:38 and 01:42 AEDT, "no, no action on adversary. no point": the bare framework's step
  `setClock p t` is not allowed at a corrupted validator. This is the alternative of P2 in the section "Points for
  Roberto".
- D-RSV2-12 (b), 29 Oct at 01:42 AEDT, "when a validator is corrupted clock and state are set to empty": the bare
  framework's step `corrupt p` empties both `p`'s local state (already so) and `p`'s clock. This is the alternative of
  P12 in the section "Unknown `Local`, 29 Oct".

### Summary

- **Bare framework**, `spec` (`Spec/Protocol.lean:727`), case `setClock`: the enabling condition gains `p ∉ c.adv`.
- **Bare framework**, `spec` (`Spec/Protocol.lean:743`), case `corrupt`: the effect also sets `p`'s clock to `none`. Since `p` stays in `adv` and
  `setClock` is not enabled there, a corrupted validator has no clock from its corruption on. A validator in `adv` from
  the start (`Init` does not constrain `adv`) never has a clock.
- **Condition on executions**, `DiligentWithinR` (`Spec/Conditions.lean:300`): its clock part may now be discharged by a
  `corrupt p` step, taken while `p`'s clock still reads less than `t`, by the real time `t + ΔClockBehind` (P20). Without
  it the condition could not hold in any run where a validator is corrupted after its clock started, since the clock
  can then never come to the next reading.
- **Condition on executions**, `ClockWithinSkewR`: checked, its Lean text unchanged. It reads `setClock` steps only, and
  there is none at a corrupted validator; its docstring now says so.
- **Bare framework**, `Execution.Up`, `Execution.Honest`, `Execution.Enabled` (`Spec/Execution.lean`): checked,
  unchanged. None reads the clock.
- Docstrings updated, in plain words: the bare framework's `Config.clock`, `Config.adv`, `Config.crashed`,
  `Action.setClock`, `Action.corrupt`, the function `setClock` (no longer "the only write of `Config.clock`"), `spec`,
  `Init`, the module headers of `Spec/Protocol.lean`, `Spec/Execution.lean` and the root `RStsVariant2.lean`; the
  bare framework's notation `Time` (`Spec/Message.lean`); the section "Clocks and real time" of `Spec/Conditions.lean`.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. `#print axioms` on `spec`, `Step`, `system`,
`DiligentWithinR`, `ClockWithinSkewR`, `Execution.Enabled`: `[propext, Classical.choice, Quot.sound]`; on `nodeSpec`,
`nodeStep_total`: `[propext, Quot.sound]`. No `sorry`, `axiom`, `native_decide` or `variable`.

### Bare framework: `spec`, case `setClock`, before and now

Before (`Spec/Protocol.lean:713` at `9fcd8426a`):

```lean
| .setClock p t => {
    Enabled c :=
      match c.clock p with
      | some r => r < t
      | none => True
    Effect c c' := c' = setClock p t c
    feasible _ _ := ⟨_, rfl⟩ }
```

Now (`Spec/Protocol.lean:727`):

```lean
| .setClock p t => {
    Enabled c :=
      p ∉ c.adv ∧
        match c.clock p with
        | some r => r < t
        | none => True
    Effect c c' := c' = setClock p t c
    feasible _ _ := ⟨_, rfl⟩ }
```

Read aloud: the environment may set `p`'s clock to the reading `t` only when `p` is not corrupted, and then either `p`'s
clock reads less than `t`, or it does not exist yet; the step sets it to read `t`. It may do so whether `p` is up or
crashed, and before `p` has come online.

### Bare framework: `spec`, case `corrupt`, before and now

Before (`Spec/Protocol.lean:727` at `9fcd8426a`):

```lean
| .corrupt p => {
    Enabled c := p ∉ c.adv
    Effect c c' := c' = { c.setNode p none with adv := insert p c.adv }
    feasible _ _ := ⟨_, rfl⟩ }
```

Now (`Spec/Protocol.lean:743`):

```lean
| .corrupt p => {
    Enabled c := p ∉ c.adv
    Effect c c' := c' =
      { c.setNode p none with
          adv := insert p c.adv
          clock := fun q => if p = q then none else c.clock q }
    feasible _ _ := ⟨_, rfl⟩ }
```

Read aloud: the environment may corrupt `p` when `p` is not yet corrupted; then `p` joins the corrupted set for good, and
both `p`'s local state and `p`'s clock become empty (`none`), every other validator's left as it was. Neither is set
again: `restart` and `setClock` are not enabled at a corrupted validator.

### Condition on executions: `DiligentWithinR`, before and now

Before (`Spec/Conditions.lean:281` at `9fcd8426a`):

```lean
∀ (t : Time) (p : Node), (∃ (k : Nat) (t' : Time), x[k].clock p = some t' ∧ t' < t) →
  ∃ i : Nat, x.lbl i = .setClock p t ∧
    (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
    (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))
```

Now (`Spec/Conditions.lean:300`):

```lean
∀ (t : Time) (p : Node), (∃ (k : Nat) (t' : Time), x[k].clock p = some t' ∧ t' < t) →
  ∃ i : Nat,
    (x.lbl i = .setClock p t ∧
      (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
      (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
        ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
          (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
            ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))) ∨
    (x.lbl i = .corrupt p ∧ (∃ t' : Time, x[i].clock p = some t' ∧ t' < t) ∧
      x.stamp (i + 1) ≤ t + ΔClockBehind)
```

Read aloud: this is a condition on executions, which the bare framework does not assume. For every node `p`, once `p`'s
clock has started at some reading `t₀`, then for every reading `t` greater than `t₀`, either `p`'s clock comes to read
`t` between the real times `t − ΔClockAhead` and `t + ΔClockBehind`, and `p`, if up and honest at that moment, then
takes its timer interrupt at the reading `t` by the real time `t + ΔClockBehind`, unless it is corrupted or crashed
first; or `p` is corrupted while its clock still reads less than `t`, by the real time `t + ΔClockBehind`. The first
reading `t₀` may be any reading, and a clock that never starts is asked nothing.

The premise is unchanged. A configuration where `p`'s clock exists is one where `p` is not corrupted (the bare
framework's `corrupt` empties the clock and its `setClock` is not enabled at a corrupted validator; read off the step
relation, not proved), so the premise already reads only configurations where `p` is not corrupted (T21).

### Points for Roberto, the new default

**P20. How the condition on executions `DiligentWithinR` releases a validator corrupted before its clock reaches a
reading.** Default: its clock part for the reading `t` is discharged by a step `corrupt p` taken while `p`'s clock still
reads less than `t`, at a real time at most `t + ΔClockBehind`.

- Default, (a), as landed. What it does: a validator that is corrupted before its clock comes to `t` owes nothing for
  `t`, provided the corruption comes by the end of `t`'s window. Pros: it is the same deadline as the corruption that
  excuses a missing tick in the tick part; a validator still not corrupted at the real time `t + ΔClockBehind` owes the
  change to `t`, as before. Cons: one more disjunct in the condition, and a statement that uses the condition has one
  more case.
- Alternative, (b): the `corrupt p` step discharges the reading `t` at any real time, with no deadline. What it does:
  the clock part asks the change to `t` only of a validator never corrupted while its clock reads less than `t`. Pros:
  one fewer conjunct. Cons: a run where a validator's clock stands still for a long time and the validator is corrupted
  much later satisfies the condition for every reading it skipped meanwhile, so the condition no longer bounds an
  honest validator's clock while it is honest.
- Alternative, (c): the premise also asks that `p` is never corrupted in the run (`∀ k, p ∉ x[k].adv`). What it does:
  the condition asks nothing of any validator that is ever corrupted. Pros: the conclusion keeps its old shape. Cons: a
  validator corrupted late in a run is asked nothing even for the readings while it was honest, which a statement about
  validators honest up to some real time cannot then use.

Reply words: D-RSV2-23 (a), (b) or (c). The code D-RSV2-23 is this lane's proposal; the coordinator assigns the code it
uses.

### Effect on earlier sections

- P2 ("`setClock` is enabled for a corrupted node too", section "Points for Roberto") and P12 ("whether a corrupted
  validator's clock goes on existing", section "Unknown `Local`, 29 Oct") are settled by their alternatives. Their text
  is left as it was.
- The section "A restart needs the clock, 29 Oct" says that "no step makes a clock absent again"; `corrupt` now does. Its
  conclusion still holds: a known local state comes with a clock, since `corrupt` empties both at once. Its text is
  left as it was.

### Taken, tell me to revisit

- **T21. The premise of `DiligentWithinR` gains no `p ∉ x[k].adv`.** It is implied by the bare framework (a clock that
  exists belongs to a validator not corrupted), so adding it would change nothing. The alternative was to add it, so
  that a reader sees it without the bare framework; the brief offered it as an example.
- **T22. The tick part's `p ∉ x[i].adv` is kept**, although it is now implied at a `setClock p t` step (that step is
  enabled only at a validator not corrupted). The tick part is unchanged as landed.
- **T23. `corrupt`'s write of the clock is written inline in `spec`**, `clock := fun q => if p = q then none else
  c.clock q`, rather than through a new helper beside the function `setClock`. The function `setClock`'s docstring names
  `corrupt` as the other write of `Config.clock`.
- **T24. The edit block and the splice script** are committed in `scratch/rsts2h/edits/`, the ledger and the checks in
  `scratch/rsts2h/`.

## D-RSV2-6 (b), 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2i` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_split_diligent.md`. Definitions only. Conditions on executions only:
the bare framework (`Spec/Protocol.lean`, `Spec/Execution.lean`) does not change, except docstrings that named
`DiligentWithinR`.

Amended at 02:01 AEDT by the coordinator, relaying Roberto ("add docstring like the above to the definition to explain
clause by clause"): the docstring of each of the three definitions quotes its formula clause by clause, in order, each
clause a short Lean fragment followed by "Read aloud:", and says why the real time of step `i` is `x.stamp (i + 1)` (the
stamp of the configuration the step enters; `x.stamp i` is when the configuration before it was entered).

Roberto's ruling, D-RSV2-6 (b), 29 Oct between 01:47 and 01:49 AEDT: "(b), but I don't think we should constrain the
clock of crashed nodes". The condition on executions `DiligentWithinR` becomes two conditions on executions, a clock
condition and a tick condition, and the clock condition does not constrain the clock of a crashed or corrupted
validator. This is the alternative (a) of P6 in the section "Points for Roberto" (split the clock half into a condition
of its own), with the clock of a crashed node released as in P6's alternative (b).

### Summary

- **`ClockAdvancesWithinR ΔClockAhead ΔClockBehind`** (`Spec/Conditions.lean:324`), the clock condition, new. It reads
  `p`'s clock only in the configurations where `p` is neither crashed nor corrupted. For each such configuration `i`
  and each reading `t` greater than the clock's reading there, either `setClock p t` is taken in `t`'s window, or `p` is
  crashed or corrupted in some configuration after `i` entered by the real time `t + ΔClockBehind`.
- **`TicksWithinR ΔClockBehind`** (`Spec/Conditions.lean:402`), the tick condition, new. It is the landed tick part,
  stated alone: for every step `setClock p t` at which `p` is up, honest and with its local state known, `p` takes
  `tick p` at the reading `t` by the real time `t + ΔClockBehind`, unless it is corrupted or crashes first. D-RSV2-5
  (a) is kept: a node restarted while its clock reads `t` is not owed a tick at `t`.
- **`DiligentWithinR ΔClockAhead ΔClockBehind`** (`Spec/Conditions.lean:439`) stays, as an abbreviation (`abbrev`) of
  the conjunction of the two (T25).
- **P20 no longer arises as posed.** The release by corruption of the section "D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct"
  is replaced by the release by a crash or a corruption in `ClockAdvancesWithinR`. Its question, by when the release
  must come, now covers a crash and a corruption together: it is P21, whose default is P20's default (a), the deadline
  `t + ΔClockBehind`. P20's alternative (c) (a premise that `p` is never corrupted) has no counterpart, since the premise
  now reads `p`'s status in one configuration.
- **A new consequence, P22**: a node is restarted only with its clock within the bounds of the real time. A crashed
  node's clock is free while it is crashed, but a configuration after its restart binds it again, so a clock that fell
  behind is brought forward by a `setClock` before the restart, or the run does not satisfy `ClockAdvancesWithinR`.
- **P23**: a validator that has not yet come online, and has not crashed, is outside `crashed`, so its clock is bound
  once started, as before this change.
- Docstrings that named `DiligentWithinR` are updated: the module header and the sections "Clocks and real time" and
  "Fairness" of `Spec/Conditions.lean`; `Spec/Execution.lean`'s module header (the paragraph "Since 29 Oct 2026");
  `Spec/Protocol.lean`'s module header (the bullet on `tick p`) and the docstring of `nodeSpec`, which now name
  `TicksWithinR`. `ClockWithinSkewR` is unchanged.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. `#print axioms` on `ClockAdvancesWithinR`,
`TicksWithinR`, `DiligentWithinR`, `ClockWithinSkewR`, `spec`, `Step`, `system`, `Execution.Enabled`:
`[propext, Classical.choice, Quot.sound]`; on `nodeSpec`, `nodeStep_total`: `[propext, Quot.sound]`. No `sorry`,
`axiom`, `native_decide` or `variable`.

### Before

`DiligentWithinR` (`Spec/Conditions.lean:300` at `c23b62767`):

```lean
∀ (t : Time) (p : Node), (∃ (k : Nat) (t' : Time), x[k].clock p = some t' ∧ t' < t) →
  ∃ i : Nat,
    (x.lbl i = .setClock p t ∧
      (t : ℝ) - ΔClockAhead ≤ x.stamp (i + 1) ∧ x.stamp (i + 1) ≤ t + ΔClockBehind ∧
      (p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
        ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
          (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
            ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n))) ∨
    (x.lbl i = .corrupt p ∧ (∃ t' : Time, x[i].clock p = some t' ∧ t' < t) ∧
      x.stamp (i + 1) ≤ t + ΔClockBehind)
```

Read aloud: for every node `p`, once `p`'s clock has started at some reading `t₀`, then for every reading `t` greater
than `t₀`, either `p`'s clock comes to read `t` between the real times `t − ΔClockAhead` and `t + ΔClockBehind`,
whether `p` is up or crashed, and `p`, if up and honest at that moment, then takes its timer interrupt at the reading
`t` by the real time `t + ΔClockBehind`, unless it is corrupted or crashed first; or `p` is corrupted while its clock
still reads less than `t`, by the real time `t + ΔClockBehind`.

### Now: the clock condition `ClockAdvancesWithinR` (`Spec/Conditions.lean:324`)

```lean
def ClockAdvancesWithinR {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockAhead ΔClockBehind : ℝ) (x : Exec Pr) : Prop :=
  ∀ (t : Time) (p : Node) (i : Nat) (t' : Time),
    p ∉ x[i].crashed → p ∉ x[i].adv → x[i].clock p = some t' → t' < t →
      (∃ j : Nat, x.lbl j = .setClock p t ∧
        (t : ℝ) - ΔClockAhead ≤ x.stamp (j + 1) ∧ x.stamp (j + 1) ≤ t + ΔClockBehind) ∨
      (∃ j : Nat, i < j ∧ x.stamp j ≤ t + ΔClockBehind ∧ (p ∈ x[j].crashed ∨ p ∈ x[j].adv))
```

Read aloud: this is a condition on executions, which the bare framework does not assume. Whenever a node `p` is neither
crashed nor corrupted in a configuration `i` and its clock there reads less than a reading `t`, either `p`'s clock
comes to read `t` between the real times `t − ΔClockAhead` and `t + ΔClockBehind`, or `p` is crashed or corrupted in
some later configuration entered by the real time `t + ΔClockBehind`. Said the other way round: if `p` stays neither
crashed nor corrupted from configuration `i` up to the real time `t + ΔClockBehind`, its clock comes to read `t` in
`t`'s window. A crashed node's clock is not read, and a clock that never starts is asked nothing.

### Now: the tick condition `TicksWithinR` (`Spec/Conditions.lean:402`)

```lean
def TicksWithinR {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockBehind : ℝ) (x : Exec Pr) : Prop :=
  ∀ (i : Nat) (p : Node) (t : Time), x.lbl i = .setClock p t →
    p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none →
      ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧
        (x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n)
```

Read aloud: this is a condition on executions, which the bare framework does not assume. Whenever a node `p`'s clock
comes to read `t` while `p` is up and honest, `p` takes its timer interrupt at the reading `t` by the real time
`t + ΔClockBehind`, unless it is corrupted or crashes first (a crash between steps, or a crash during one of its
reactions).

### Now: `DiligentWithinR` (`Spec/Conditions.lean:439`)

```lean
abbrev DiligentWithinR {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (ΔClockAhead ΔClockBehind : ℝ) (x : Exec Pr) : Prop :=
  ClockAdvancesWithinR ΔClockAhead ΔClockBehind x ∧ TicksWithinR ΔClockBehind x
```

Read aloud: both the clock condition and the tick condition hold.

### What changes for a run

- A crashed node's clock is no longer asked anything while the node is crashed: it may stand still, skip readings, or
  be set outside a reading's window (`ClockWithinSkewR`, a separate condition on executions, still bounds the real time
  of every `setClock` taken).
- A crash after a configuration that binds `p` for `t`, by `t + ΔClockBehind`, releases `t`. A crash before that
  configuration releases nothing: when `p` is restarted with its clock still reading less than `t`, the configuration
  the restart enters binds `p` for `t` again.
- A node is restarted only with its clock within the bounds of the real time (P22).
- The tick condition is the landed tick part. Stated alone, it is asked at every `setClock p t` at which `p` is up,
  honest and with its local state known; a clock comes to each reading at most once, so this is the same set of
  obligations as before.

### Points for Roberto, the new defaults

**P21 (replaces P20). By when a crash or a corruption must come to release a node from a reading `t` in the clock
condition `ClockAdvancesWithinR`.** Default: after a configuration that binds `p` for `t`, and by the real time
`t + ΔClockBehind`.

- Default, (a), as landed. What it does: a node that crashes or is corrupted after a configuration where it was
  neither and its clock read less than `t`, by the end of `t`'s window, owes nothing for `t`; a node that stays
  neither crashed nor corrupted up to `t + ΔClockBehind` owes the change to `t` in `t`'s window. Pros: the same deadline
  as the crash or corruption that excuses a missing tick in `TicksWithinR`, and as P20's default; the condition then
  bounds the clock of every node that is up and honest through a window. Cons: none found beyond the extra case a
  statement using the condition handles.
- Alternative, (b): any crash or corruption after the binding configuration releases `t`, with no deadline. What it does:
  drops `x.stamp j ≤ t + ΔClockBehind`. Pros: one conjunct fewer. Cons: a node whose clock stands still while it is up,
  and which crashes much later, satisfies the condition for every reading it skipped meanwhile, so the condition no
  longer bounds the clock of a node while it is up.

Reply words: D-RSV2-23 (a) or (b). The code D-RSV2-23 was proposed for P20 and is reused here, since P20 is replaced;
the coordinator assigns the code it uses.

**P22. A node is restarted only with its clock within the bounds of the real time.** Default: a configuration binds
`p` for `t` whatever the real time it is entered at.

- Default, (a), as landed. What it does: in a configuration where `p` is neither crashed nor corrupted and its clock
  reads `t'`, the reading `t' + 1` is owed, and both ways of meeting it come after that configuration; so that
  configuration was entered by the real time `t' + 1 + ΔClockBehind` (read off the step relation, not proved). A node
  whose clock fell behind while it was crashed has it brought forward by a `setClock` (enabled while crashed, and free
  to skip readings) before its restart; otherwise the run does not satisfy the condition. Pros: in every configuration
  where a node is up and honest its clock lags the real time by at most `1 + ΔClockBehind`, restarts included, so
  no honest step runs at a reading far behind the real time. Cons: it constrains the clock at the moment of the restart,
  which is a constraint on the clock of a node coming back from a crash, though not while it is crashed.
- Alternative, (b): a configuration binds `p` for `t` only when it is entered by the end of `t`'s window, the premise
  gaining `x.stamp i ≤ t + ΔClockBehind`. What it does: a node restarted with a clock that fell behind is released from
  every reading whose window ended before the restart, and its clock must then come to the first reading whose window
  has not ended, within that window (less than one unit of real time after the restart). Pros: no constraint at all
  tied to a crash, its restart included. Cons: a node up and honest may run, for up to one unit of real time after its
  restart, at a reading far behind the real time (it may tick, and take deliveries, at that reading), so a statement
  needing an honest node's reading close to the real time must assume more.

Reply words: D-RSV2-24 (a) or (b) (the code is this lane's proposal).

**P23. A validator that has not yet come online, and has not crashed, has its clock bound once started.** Default: the
premise reads "outside `crashed` and outside `adv`", the brief's words for "neither crashed nor corrupted", so such a
validator is bound as before this change.

- Default, (a), as landed. What it does: a validator whose local state is unknown and which is not corrupted is outside
  `crashed` unless it crashed before coming online; its clock, once started, comes to every greater reading in window.
  Pros: it follows the ruling's words; the clock of a validator about to come online is current, without relying on
  P22. Cons: two validators the bare framework calls down (`Execution.Up`: crashed, or never come online) are treated
  differently, and a validator that crashes before coming online is released while one that does not is bound.
- Alternative, (b): the premise reads "up and honest" (`x.Up i p` and `x.Honest i p`: outside `crashed`, outside `adv`,
  and its local state known). What it does: the clock of a validator that has not come online is not read, as for a
  crashed one; with P22 (a), the validator comes online only with its clock within the bounds of the real time. Pros:
  the condition reads clocks exactly where the bare framework says a validator is up and honest, and treats the two
  ways of being down alike. Cons: a statement about a validator's clock before it comes online gets nothing from the
  condition (no such statement exists today).

The lane recommends (b), for the treatment of the two ways of being down alike; (a) landed because it is the brief's
wording. Reply words: D-RSV2-25 (a) or (b) (the code is this lane's proposal).

### Effect on earlier sections

- P6 ("Every clock visits every positive reading", section "Points for Roberto") is settled by the ruling. Its text is
  left as it was.
- P20 (section "D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct") is replaced by P21. Its text is left as it was.
- The section "D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct" says the clock part of `DiligentWithinR` may be discharged by a
  corruption; that is now `ClockAdvancesWithinR`'s release, with a crash added. Its text is left as it was.

### Taken, tell me to revisit

- **T25. `DiligentWithinR` stays, as an `abbrev` of the conjunction** of `ClockAdvancesWithinR` and `TicksWithinR`, so a
  statement that needs both takes one hypothesis, and the name keeps its meaning in the earlier sections. The
  alternatives: remove it, or make it a `def` (Lean would then not unfold it by itself).
- **T26. The premise of `ClockAdvancesWithinR` names `p ∉ x[i].adv`**, although a configuration where `p`'s clock exists
  is one where `p` is not corrupted (T21 left it out of the old premise). Here the premise is about `p`'s status, and
  "neither crashed nor corrupted" reads off it directly. The alternative was to leave it out.
- **T27. The release is read off configurations**, `p ∈ x[j].crashed ∨ p ∈ x[j].adv` in a configuration `j` after `i`
  entered by `t + ΔClockBehind`, rather than off step labels. Only `crash p`, `crashDuring p a n` and `corrupt p` put `p`
  into those sets, so the two say the same; the configuration form is shorter. The alternative was to list the labels,
  as `TicksWithinR` does.
- **T28. `TicksWithinR` is stated for every step `setClock p t`**, not for the one in `t`'s window, and takes only
  `ΔClockBehind`. A clock comes to each reading at most once, so the obligations are those of the landed tick part.
  At a clock's first reading the validator is not yet online, so no tick is asked there, as before.
- **T29. Indices renamed by the naming checklist**: a configuration or step index is `i` or `j` (the old premise used
  `k`).
- **T31. The clause-by-clause docstrings** (the amendment) number the clauses 1 to 4 for `ClockAdvancesWithinR` (the
  premise, the disjunction, the clock change in the window, the release) and for `TicksWithinR` (the `setClock` step,
  up, honest and online there, the later step by the deadline, its four ways), then give the consequences and a closing
  "Read aloud:" for the whole. The release's `x.stamp j` is explained as the real time configuration `j` is entered.
  The alternative was one paragraph per clause without numbers.
- **T30. The edit blocks and the splice scripts** (`splice.py`, then `resplice.py` for the amendment) are committed in `scratch/rsts2i/edits/`, the ledger and the checks in
  `scratch/rsts2i/`.

## The view leaves `Local`, 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2j` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_view_out_of_local.md`. Definitions only. This changes the bare
framework (`Spec/Protocol.lean`), and the docstrings, and one formula, of conditions on executions
(`Spec/Conditions.lean`).

Roberto, 29 Oct between 02:05 and 02:12 AEDT: "ok. this is an issue. We do need to enable deliveries to corrupted nodes
and keep track of them in the node view. So view should never be empty." Before this change the view was a field of
`Local`; since D-RSV2-12 (b) `corrupt p` empties `p`'s `Local`, so a corrupted validator, and one not yet online, had no
view, and `deliver p e` needed `p` up, honest and online.

### Summary

- **Bare framework: the view is a configuration field**, `Config.view : Node → View Node Msg` (`Spec/Protocol.lean:420`).
  Every validator has a view in every configuration, whether its local state is known or unknown. `Local`
  (`Spec/Protocol.lean:366`) keeps `st` and `disk`; `Pr.initialLocal p` (`Spec/Protocol.lean:380`) no longer sets a view.
- **Bare framework: `Init` empties every view** (`Spec/Protocol.lean:929`).
- **Bare framework: a delivery to a corrupted validator is a step.** `spec`'s case `.deliver p e`
  (`Spec/Protocol.lean:828`) is the new `deliverSpec` (`Spec/Protocol.lean:773`): at an honest `p`, the node action of a
  delivery as before (`nodeSpec`, unchanged); at a corrupted `p`, enabled when `e` is on the wire and names `p` among its
  recipients, crashed or not, and its effect files `e`'s signed message into `p`'s view and runs no protocol code.
- **Bare framework: `receive`** (`Spec/Protocol.lean:570`) writes `Config.view`, whatever `p`'s local state.
- **Bare framework: `corrupt p` and `restart p keep` leave the view as it was**, with no change to their formulas: the
  view is no longer in what `setNode` replaces.
- **Condition on executions: `NodeStepsAtIncreasingTimesR`** (`Spec/Conditions.lean:208`) counts a node's steps only
  while the node is honest (two premises added, P27), so deliveries to a corrupted validator may share a real time.
- **Conditions on executions: `PositiveDeliveryDelayR`** (`Spec/Conditions.lean:233`), **`DeliverFair`**
  (`Spec/Conditions.lean:487`) and **`DeliveredBeforeActing`** (`Spec/Conditions.lean:590`): formulas unchanged; their
  docstrings now say what each means for a corrupted recipient (P25, P28). `Action.RunsCodeOf`
  (`Spec/Conditions.lean:175`): formula unchanged, docstring says it reads the label alone.
- **Docstrings**: the module header of `Spec/Protocol.lean` (a new section "Views", the sections "Unknown local state"
  and "Crash and restart"), `Config`'s fields `nodes`, `adv` and `crashed`, `Action` and its cases `deliver`, `corrupt`,
  `restart`, `NodeAction.prepare`, `nodeSpec`, `spec`; the module header and the reading paragraph of
  `Spec/Execution.lean`; the module header of `Spec/Conditions.lean`.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings, first try. `#print axioms` on `deliverSpec`, `nodeSpec`,
`Init`, `receive`, `Protocol.initialLocal`, `nodeStep_total`: `[propext, Quot.sound]`; on `spec`, `Step`, `system`,
`Execution.Enabled`, `NodeStepsAtIncreasingTimesR`, `PositiveDeliveryDelayR`, `DeliverFair`, `DeliveredBeforeActing`:
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom`, `native_decide` or `variable`.

### The new forms

Bare framework, `Config`'s new field (`Spec/Protocol.lean:420`):

```lean
  view : Node → View Node Msg
```

Read aloud: each validator's view, the set of signed messages delivered to it so far; every validator has one in every
configuration, corrupted validators included.

Bare framework, `Local` (`Spec/Protocol.lean:366`), with the field `view` removed:

```lean
structure Local (Node Msg NodeState : Type) where
  st : NodeState
  disk : NodeState
```

Read aloud: what a validator holds locally is its memory and its disk.

Bare framework, `receive` (`Spec/Protocol.lean:570`):

```lean
def receive {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg] (p : Node)
    (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) : Config Node Msg NodeState :=
  { c with view := fun q => if p = q then insert m (c.view p) else c.view q }
```

Read aloud: `m` is added to `p`'s view, and nothing else changes.

Bare framework, `deliverSpec` (`Spec/Protocol.lean:773`), the case `.deliver p e` of `spec`:

```lean
def deliverSpec {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Envelope Node Msg) :
    ActionSpec Node Msg NodeState where
  Enabled c :=
    (p ∈ c.adv ∧ e ∈ c.sent ∧ e.recipients.Has p) ∨ (nodeSpec Pr p (.deliver e)).Enabled c
  Effect c c' :=
    (p ∈ c.adv ∧ c' = receive p e.toSignedMsg c) ∨
      (p ∉ c.adv ∧ (nodeSpec Pr p (.deliver e)).Effect c c')
```

Read aloud: a sent envelope addressed to `p` may be delivered to `p` when `p` is corrupted, crashed or not, and is then
only filed into `p`'s view; or when `p` is up and honest with its local state and clock reading known, and `p` then
reacts to it at its clock reading as its protocol permits, after it is filed into `p`'s view.

Bare framework, `Init` (`Spec/Protocol.lean:929`):

```lean
def Init {Node Msg NodeState : Type} (c : Config Node Msg NodeState) : Prop :=
  (∀ p : Node, c[p] = none) ∧ (∀ p : Node, c.clock p = none) ∧ (∀ p : Node, c.view p = ∅) ∧
    c.sent = 0
```

Read aloud: every validator's local state is unknown, no validator's clock exists, every validator's view is empty, and
nothing has been sent.

Condition on executions, `NodeStepsAtIncreasingTimesR` (`Spec/Conditions.lean:208`):

```lean
  ∀ (i j : Nat) (p : Node), i < j → (x.lbl i).RunsCodeOf p → (x.lbl j).RunsCodeOf p →
    p ∉ x[i].adv → p ∉ x[j].adv →
    x.stamp (i + 1) < x.stamp (j + 1)
```

Read aloud: this is a condition on executions, which the bare framework does not assume. Whenever an honest `p` takes a
step at `i` and another at a later `j`, still honest, the real time of the second is strictly greater than the real time
of the first.

### Points for Roberto, 29 Oct

**P24. Deliveries to a crashed honest validator, or to an honest one not yet online.** The bare framework's
`deliverSpec`, honest case. Default: not enabled, as before.

- Default, (a), as landed. What it does: an honest validator is delivered messages only while it is up, with its local
  state known; its view holds exactly the messages it reacted to (and the ones whose reaction a `crashDuring`
  interrupted). Pros: the view of an honest validator and its reactions stay in step; `DeliveredBeforeActing` and
  `DeliverFair` read as before for honest recipients. Cons: what the network brings an honest validator while it is down
  leaves no trace in its view; the network is owed it again after the restart (`DueBy`'s catch-up deadline).
- Alternative, (b): enabled, filing into the view only, as at a corrupted validator. What it does: `deliverSpec` gains a
  third case, `p` honest and down, whose effect is `receive` alone. Pros: the view records everything the network brought
  the validator, up or down, the same way for every validator. Cons: the view of an honest validator then holds messages
  it never reacted to; `DeliveredBeforeActing` must then say that the delivery it asks for was to `p` while up;
  `DeliverFair` then asks for deliveries to a down validator; `NodeStepsAtIncreasingTimesR` must not count them.

Reply words: D-RSV2-26 (a) or (b) (the code is this lane's proposal).

**P25. What `DeliverFair` and `DeliveredBeforeActing`, conditions on executions, say of corrupted recipients.** Default:
as their formulas read after the change, said in their docstrings.

- Default, (a), as landed. What it does: `DeliverFair` is weak fairness of every `deliver p e`, so it now also covers a
  corrupted `p`; such a delivery stays enabled once `e` is sent (corruption is permanent, the sent log only grows), so
  every envelope addressed to a corrupted validator is delivered to it, and is delivered again after every step, as an
  envelope to an honest validator that stays up already is. `DeliveredBeforeActing` promises a corrupted validator
  nothing, since a corrupted validator takes no acting step, and the delivery it asks for is to `p` while honest. Pros:
  the view of a corrupted validator comes to hold every message addressed to it, which is what the ruling asks the view
  to track; no formula changes. Cons: a statement taking `DeliverFair` now also constrains the network's deliveries to
  the adversary (runs satisfying it exist; nothing in the adversary's step reads its view).
- Alternative, (b): `DeliverFair` restricted to recipients never corrupted (a premise `∀ i, p ∉ x[i].adv`). What it
  does: no delivery to a corrupted validator is forced. Pros: fairness speaks of honest progress only. Cons: the view of
  a corrupted validator may miss a message addressed to it forever, which goes against "keep track of them in the node
  view".

Reply words: D-RSV2-27 (a) or (b) (the code is this lane's proposal).

**P26. A delivery to a corrupted validator is enabled whether it is crashed or not.** The bare framework's `deliverSpec`,
corrupted case. Default: crashed or not, the brief's wording ("enabled also when `p ∈ c.adv`, with `e ∈ c.sent` and
`e.recipients.Has p`").

- Default, (a), as landed. What it does: `p ∉ c.crashed` is not asked of a corrupted recipient. Pros: a corrupted
  validator that crashed never leaves `crashed` (`restart` is not enabled at a corrupted validator), so under (b) its
  view would stop growing for good; a crash of a corrupted validator then has no effect on its view, as it has none on
  what the adversary can send. Cons: "crashed means it receives nothing" holds only for honest validators.
- Alternative, (b): enabled only when `p ∉ c.crashed`. What it does: adds that condition to the corrupted case. Pros:
  every crashed validator receives nothing. Cons: a corrupted validator crashed once has a view frozen from then on, and
  `DeliverFair` asks nothing for it.

Reply words: D-RSV2-28 (a) or (b) (the code is this lane's proposal).

**P27. `NodeStepsAtIncreasingTimesR`, a condition on executions, counts a node's steps only while it is honest.**
Default: the premises `p ∉ x[i].adv` and `p ∉ x[j].adv` added.

- Default, (a), as landed. What it does: two deliveries to a corrupted validator may share a real time; every other step
  the condition counts is enabled only at an honest validator, so for honest validators nothing changes. Pros: the
  condition stays about a node's program, and a delivery to a corrupted validator runs none. Cons: one premise more than
  needed (`p ∉ x[j].adv` alone implies the other, corruption being permanent); written out so that it reads "honest at
  both steps".
- Alternative, (b): the formula as before. What it does: deliveries to a corrupted validator are at strictly increasing
  real times, and strictly after any earlier step of the validator while honest. Pros: no change to the formula. Cons:
  it constrains steps that run no code, against the condition's own reading, and two messages delivered to the
  adversary at one real time become a run the condition excludes.

Reply words: D-RSV2-29 (a) or (b) (the code is this lane's proposal).

**P28. `PositiveDeliveryDelayR`, a condition on executions, covers deliveries to a corrupted validator.** Default: as its
formula reads, said in its docstring.

- Default, (a), as landed. What it does: every delivery, to an honest or a corrupted validator, is strictly later than a
  sending of the envelope; no view comes to hold a message at the real time the message is first sent. Pros: one rule
  for every delivery; no formula changes. Cons: the view of a corrupted validator cannot record a message at the real
  time it is sent, as a rushing adversary of the literature would see it; this limits nothing the adversary can send,
  since its step does not read its view.
- Alternative, (b): deliveries to a corrupted validator are exempt (a premise `p ∉ x[j].adv`). What it does: the view of
  a corrupted validator may record a message at the real time it is sent. Pros: matches a rushing adversary. Cons: one
  case more in the condition, read only by a statement that reads a corrupted validator's view at a sending's real time
  (none exists today).

Reply words: D-RSV2-30 (a) or (b) (the code is this lane's proposal).

### Effect on earlier sections

- The section "Unknown `Local`, 29 Oct" says `Pr.initialLocal p` gives an empty view, and that a crashed validator keeps
  its view as part of its `Local`; the view is now `Config.view`, untouched by a restart and kept by a crash. Its text is
  left as it was.

### Taken, tell me to revisit

- **T32. `deliverSpec` is a named definition beside `nodeSpec`**, and `nodeSpec` is unchanged (honest only). So
  `crashDuring`, whose enabling condition is `nodeSpec`'s, is still never enabled at a corrupted validator, which has no
  reaction to interrupt. The alternatives: write the case inline in `spec`, or add the corrupted case to `nodeSpec`
  (which would enable `crashDuring` at a corrupted validator).
- **T33. Each case of `deliverSpec`'s effect carries its own condition on `p ∈ c.adv`**, so the effect does not rely on
  a corrupted validator's local state being unknown (true of every reachable configuration, but not a fact `Effect`
  can read). The alternative was the two effects joined without the condition.
- **T34. `receive` writes `Config.view` directly**, with no setter `Config.setView`: it is the one writer of the view.
  The alternative was a setter mirroring `Config.setNode`.
- **T35. The two `feasible` proofs that read `(na.prepare p c)[p]`** (in `nodeSpec` and in `spec`'s case
  `crashDuring`) now close by `exact ⟨l, hl⟩`: `receive` no longer touches the local state, so the prepared
  configuration's `[p]` is `c[p]` by definition. They used `simp [NodeAction.prepare, receive, hl]`.
- **T36. Unchanged**: `DueBy` (it reads restarts of `p`, which a corrupted `p` never takes, and is read only by
  `DeliveredBeforeActing`), `ClockWithinSkewR`, `ClockAdvancesWithinR`, `TicksWithinR`, `WeakFair`, `StrongFair`,
  `CustomFair`, `Execution.Up`, `Execution.Enabled`, and the formulas of `PositiveDeliveryDelayR`, `DeliverFair`,
  `DeliveredBeforeActing`, `Action.RunsCodeOf`.
- **T37. Each changed docstring of `Spec/Conditions.lean` now opens with "A condition on executions, not part of the
  bare framework"** and its closing "Read aloud:" with "this is a condition on executions, which the bare framework does
  not assume", as `ClockAdvancesWithinR`'s does (Roberto's rule of 29 Oct on labels).
- **T38. The edit scripts were Python string replacements run in place**, not kept as files; the pages before the edit
  are in `scratch/rsts2j/check/`, with the ledger and the build logs in `scratch/rsts2j/`.

## D-RSV2-26 (a), 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2k` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_cleanup.md`, on `dev` at `474ddfd5a`. Definitions only.

Roberto's ruling: "26 (a), but do not remove the weak and strong fairness ones" (29 Oct, about 02:25), after the
coordinator amended option (a) to keep `Execution.InForce`, which phase C's projection on `RStsVariant` reads in its
counterpart.

### Summary

- **Removed, because nothing in `RStsVariant2` uses them and no statement takes them yet.** From `Spec/Conditions.lean`
  the properties of executions `Safe`, `Live`, `Secure`, and the conditions on executions `DeliverFair`, `CustomFair`,
  `CorruptionBounded`. From the bare framework, `Execution.Up` (`Spec/Execution.lean`), which only `Live` read.
- **Removed, because no definition needs them.** The `rfl` lemmas `nodes_apply` and `Config.setNode_apply`
  (`Spec/Protocol.lean`) and `Addressed.addressed_sign` (`Spec/Message.lean`). No proof on the pages calls them by name,
  and none uses `simp`, so none uses them as `simp` lemmas either.
- **Kept.** `WeakFair` (`Spec/Conditions.lean:245`) and `StrongFair` (`Spec/Conditions.lean:254`), on Roberto's word;
  `Execution.Enabled` (`Spec/Execution.lean:160`), which they read; `Execution.InForce` (`Spec/Execution.lean:114`);
  `Execution.Honest` (`Spec/Execution.lean:145`); every other condition on executions; and the theorem `nodeStep_total`
  (`Spec/Protocol.lean:635`), because the definition `nodeSpec` needs it: its `feasible` field's proof ends with
  `exact nodeStep_total …` (`Spec/Protocol.lean:738`), and `deliverSpec`'s and `spec`'s `feasible` read `nodeSpec`'s.
- **D-RSV2-10 no longer arises.** It asked how `Execution.Up` should read a validator that has never come online (P10 in
  the section "Unknown `Local`, 29 Oct"). With `Execution.Up` removed, no definition of `RStsVariant2` says what "up"
  means; `ClockAdvancesWithinR` and `TicksWithinR` read `crashed`, `adv` and the local state directly, as before. A
  statement that needs a validator up states its own condition on those fields.
- **`Spec/Conditions.lean` now holds conditions on executions only**, so its title is "Conditions on executions" and its
  module header lists them in one sentence.

Build: `lake build RStsVariant2`, exit 0, 0 errors, 0 warnings. `#print axioms` on `nodeStep_total`, `nodeSpec`,
`deliverSpec`, `Init`, `receive`, `Protocol.initialLocal`, `Envelope.addressed`: `[propext, Quot.sound]`; on `spec`,
`Step`, `system`, `Execution.InForce`, `Execution.Honest`, `Execution.Enabled` and every condition on executions:
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom`, `native_decide` or `variable`. A probe
(`scratch/rsts2k/check/removed.lean`) confirms that each of the ten removed names is now unknown.

### Docstrings and module headers changed

- `Spec/Conditions.lean`, module header: the list of conditions without `CorruptionBounded`, `DeliverFair`,
  `CustomFair`, and without the bullet "Properties of executions"; the paragraph on deliveries to corrupted validators
  no longer names `DeliverFair`.
- `Spec/Conditions.lean`, section "The environment": a model that needs a node to participate throughout a real-time
  window states a condition of its own on the configurations in force during the window (`Execution.InForce`), for
  example that the node is outside `crashed` and its local state is known in each. It said "states that it is up
  (`Execution.Up`)".
- `Spec/Conditions.lean`, section "Security properties": removed with the three properties.
- `Spec/Execution.lean`, module header: the list of the page's definitions without `Execution.Up`; the sentence on the
  properties of executions removed; the paragraph "Since 29 Oct 2026" no longer says how `Execution.Up` counts a
  validator never online.
- `Spec/Execution.lean`, section "Reading an execution": the sentence on `x.Up i p` removed.
- `Spec/Protocol.lean`, module header: the sentence saying the two `rfl` read-backs stay is replaced by "No other
  theorem is on this page." It names no removed lemma, so that no removed name stays on the pages.
- `Spec/Protocol.lean`, `Config.setNode`'s docstring: the clause pointing to the removed `Config.setNode_apply` becomes "with a
  value `(c.setNode p r)[q]` is `if p = q then r else c[q]` by definition".

### Points for Roberto

**P29. `Envelope.addressed` (`Spec/Message.lean:92`) is now used by nothing.** Its only user was the removed lemma
`Addressed.addressed_sign`. Default: kept, since the ruling names it not and it is a definition, not a lemma. Pros:
nothing outside the ruling changes. Cons: one more definition that nothing reads. Alternative: remove it too. Pros: the
page holds only what something uses. Cons: a removal not in the ruling.

### Taken, tell me to revisit

- **T39. `DeliverFair` and `CustomFair` are removed**, read as instances of `WeakFair` and not among "the weak and
  strong fairness ones" (taken by the coordinator in the brief).
- **T40. The `Spec/Conditions.lean` title loses "and properties of executions"** and its header becomes one sentence,
  since the page now holds one kind of definition. The alternative was to keep the two-bullet shape with one bullet.
- **T41. The earlier sections of this file are not edited**, except a one-line note at P10. They say what each lane
  landed; the names they mention as present (`Execution.Up`, `Live`, `DeliverFair`, …) were present then.
- **T42. The edits were scripted** (`scratch/rsts2k/edit_conditions.py`, `scratch/rsts2k/edit_others.py`), with two line
  reflows by hand; the pages before the edit are in `scratch/rsts2k/check/`.

## D-PHC8 (d), 29 Oct

Roberto, 29 Oct between 03:16 and 03:28 AEDT: "go with (d) but add to the  top of the todos that this is something to sort out in the future as even (d) looks messy". Landed by the coordinator.

| definition | before | after |
| --- | --- | --- |
| `Protocol.init` (the bare framework, a field every protocol supplies) | `Node → NodeState` | `Time → Node → NodeState`: the state a validator starts with when it comes online, given its clock reading then |
| `Protocol.initialLocal` | `Pr.initialLocal p := { st := Pr.init p, disk := Pr.persist (Pr.init p) }` | `Pr.initialLocal p t := { st := Pr.init t p, disk := Pr.persist (Pr.init t p) }` |
| `spec`, `.restart p keep`, the unknown-local-state branch | `Pr.initialLocal p` | `Pr.initialLocal p t`, `t` the stored reading the step already takes from `c.clock p = some t` |

Docstrings changed with them: the page header's bullet on `restart`, `Protocol.restart` (its `init r p` example), `Local`, `Action.restart`, the comment in `spec`, `Init`. Check: `lake build RStsVariant2` exit 0, 0 errors, 914 jobs; `scratch/rsts2_usage/usage.lean` and `scratch/sts_variant/statement_review/probe_04_v6.lean` compile with 0 errors (neither defines `init`). TODO item 73 records that the shape is to be revisited.

## D-ADQ3 (d), D-TSV7 (b), D-RTS2 (a), 29 Oct

Written 29 Oct 2026 (Sydney) by the lane `rsts2-net` (campaign `sts-variant`, Opus 5.5), from the brief
`experiments/sts-variant/briefs/brief_rstsvariant2_network_conditions.md`, on `dev` at `c7471c58f`. Definitions only.

Roberto's ruling: "D-ADQ3 (d), D-TSV7 (b), D-RTS2 (a)" (29 Oct), after the three were posed as one set in
`experiments/goldilocks/network_conditions_repose.md` section 7: the network's condition split three ways, each deadline a
function of the message and of the real time it counts from, a delay per message.

### Summary

- **The network's one condition is now three conditions on executions** (`Spec/Conditions.lean`, section "Network"); the
  bare framework (`Spec/Protocol.lean`, `Spec/Execution.lean`) assumes none of them and is not changed:
  `DeliveredBeforeActing dl` (fresh deliveries to a node up from the sending to its acting step),
  `CatchUpAfterRestart dl dlW` (what a node that restarted after the sending is owed: the restart clause of the old
  `DueBy`, separated), `SyncedWithinBy serves sync` (what an honest node that is up serves reaches every node up and
  honest until the sync deadline).
- **Each deadline is a function** `(m : Msg) → (t : ℝ) → ℝ` of the message and of the real time it counts from, with two
  instances beside the conditions: `syncDeadline tGST ΔDelay` and `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd`,
  where `ΔDelay : (m : Msg) → ℝ` is a delay per message.
- **Three readings of an execution** that the conditions use, in the same section: `Execution.ActingStep`,
  `Execution.UpBetween`, `Execution.UpAndHonestThroughout`. "Up" is read as outside `crashed` with the local state known
  (T43).
- **`scratch/sts_variant/statement_review/probe_04_v6.lean`** no longer defines its own network conditions: its
  `NetworkOutside` and `SyncOutside` are the instances of `DeliveredBeforeActing` and `SyncedWithinBy` at
  `deadlineOutside`, and its point P2 is marked settled.

Build: `lake build RStsVariant2` (through `scratch-tracked/tools/build_capped.sh`), exit 0, 0 errors, 914 jobs. `#print
axioms` on each of the nine new definitions: `[propext, Classical.choice, Quot.sound]`
(`scratch/rsts2_net/check/axioms.out`). No `sorry`, `axiom`, `native_decide` or `variable`. `probe_04_v6.lean` and
`scratch/rsts2_usage/usage.lean` compile with `lake env lean`, exit 0, 0 errors; the probe's `#check` output is unchanged.

### Before and after

Read aloud of each new form: in its docstring, `Spec/Conditions.lean`.

| definition | before | after |
| --- | --- | --- |
| `DueBy` (`Spec/Conditions.lean:509`) | `DueBy gst delta deltaW x i k p e t`: `e` sent at step `i`, `max (x.stamp (i + 1)) gst + delta ≤ t`, and for every restart of `p` (either kind) at a step `l` strictly between `i` and `k`, `max (x.stamp (l + 1)) gst + deltaW ≤ t` | `DueBy dl x i e t`: `e` sent at step `i`, and `dl e.msg (x.stamp (i + 1)) ≤ t`; no restart clause, no `k`, no `p` |
| `DeliveredBeforeActing` (`:581`) | `DeliveredBeforeActing gst delta deltaW x`: at every acting step `k` of `p`, every envelope addressed to `p`, sent at `i < k`, `DueBy gst delta deltaW x i k p e (x.stamp (k + 1))`, was delivered at `j < k` with no `restart p false` strictly between `j` and `k` | `DeliveredBeforeActing dl x`: the same, for the envelopes with `x.UpBetween i k p` (`p` up in every configuration from `i` to `k`) and `DueBy dl x i e (x.stamp (k + 1))` |
| `CatchUpAfterRestart` (`:661`) | none (the restart clause of `DueBy`) | `CatchUpAfterRestart dl dlW x`: at every acting step `k` of `p`, every envelope addressed to `p`, sent at `i < k`, with some restart of `p` (either kind) strictly between `i` and `k`, `DueBy dl x i e (x.stamp (k + 1))`, and `dlW e.msg (x.stamp (l + 1)) ≤ x.stamp (k + 1)` for every restart of `p` at a step `l` strictly between `i` and `k`, was delivered at `j < k` with no `restart p false` strictly between `j` and `k` |
| `SyncedWithinBy` (`:736`) | none | `SyncedWithinBy serves sync x`: for every real time `t`, the configuration `i` in force at `t`, every node `p` outside `crashed` and `adv` there with local state `l` and clock reading `tClock` such that `serves tClock l.st m`, and every node `p'` with `x.UpAndHonestThroughout t (sync m t) p'`: some step `j` delivers to `p'` an envelope from `p` carrying `m`, at a real time at most `sync m t`, before every acting step of `p'` at or after `sync m t`, and no earlier than a configuration `i'` entered before `t` in which `p` serves `m` |
| `syncDeadline` (`:472`) | none (inlined in `DueBy` as `max σ gst + delta`) | `syncDeadline tGST ΔDelay m t := max t tGST + ΔDelay m` |
| `deadlineOutside` (`:482`) | none | `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd m t`: `max t tGST + ΔDelay m` when at most `tAsyncStart`, otherwise `max t (max tAsyncEnd tGST) + ΔDelay m` |
| `Execution.ActingStep` (`:428`) | none (inlined in `DeliveredBeforeActing`) | `tick p`, `custom p ev`, `crashDuring p .tick n`, `crashDuring p (.custom ev) n`: the four labels the old antecedent listed |
| `Execution.UpBetween` (`:444`) | none | `∀ l, i ≤ l → l ≤ k → p ∉ x[l].crashed ∧ x[l][p] ≠ none` |
| `Execution.UpAndHonestThroughout` (`:461`) | none | in every configuration `i` with `t ≤ x.stamp (i + 1)` and `x.stamp i ≤ t'`: `p ∉ x[i].crashed ∧ x[i][p] ≠ none ∧ x.Honest i p` |

The old promise in the new terms: `DeliveredBeforeActing gst delta deltaW x` of the old page says what
`DeliveredBeforeActing (syncDeadline gst (fun _ => delta)) x ∧ CatchUpAfterRestart (syncDeadline gst (fun _ => delta))
(syncDeadline gst (fun _ => deltaW)) x` says. Argued, not machine-checked on `RStsVariant2` (P30): an envelope sent at
`i` to a node `p` acting at `k` either has `p` up in every configuration from `i` to `k`, and then no restart of `p` lies
between them (a restart is enabled only at a crashed node or one not yet online), or has `p` crashed or not yet online in
one of them, and then a restart of `p` lies strictly between `i` and `k` (`p` acts at `k`, so it is up there). The
package's probe proved the same split over `RStsVariant` (`scratch/sts_variant/package/probe_package.lean`, section 5).

"Every restart, the first coming online included", the old `DueBy`'s reading, is in `CatchUpAfterRestart`'s clauses 2
and 4: the restart that brings `p` online is a `restart p keep` like any other.

### Docstrings and module headers changed

- `Spec/Conditions.lean`, module header: the list of conditions names the network's three, with `DueBy`, the two
  deadline functions and the three readings; the section "What differs from `RStsVariant`" says the network's one
  condition is three here; the paragraph on deliveries to corrupted validators says the network's conditions never meet
  them.
- `Spec/Conditions.lean`, section "Network": rewritten (the three conditions, deadlines as functions, what "up" means);
  the remark on a future `gossiped` filter kept.
- `Spec/Execution.lean:72` (`Execution`'s docstring): "the network's conditions on executions (`DeliveredBeforeActing`,
  `CatchUpAfterRestart`, `SyncedWithinBy`) speak of delivery steps", in place of "`DeliveredBeforeActing` speaks of".
- `Spec/Protocol.lean:236` (the page header): the promise to a restarted validator is named as "the conditions on
  executions `DeliveredBeforeActing` and `CatchUpAfterRestart`".
- `Spec/Protocol.lean:432` (`Config.sent`): "what `DueBy` reads, part of the conditions on executions
  `DeliveredBeforeActing` and `CatchUpAfterRestart`", in place of "the condition on executions `DueBy`".

### Dense time

The three conditions, `DueBy` and the three readings read the stamps `x.stamp`, the labels `x.lbl` and the
configurations `x[i]` only. None of the premises of `.claude/skills/dense-time-transfer/SKILL.md` section 2 is used: no
activity constant on a unit or changing only at integer times (being up is read in every configuration, at whatever
real time it is entered); no environment step at integer times only (a crash, a restart, a corruption is a step at its
own stamp); no shared clock (no condition here reads a clock, except `SyncedWithinBy`, which hands each holder's own
reading to `serves`); no order between a delivery and a tick at one real time (steps sharing a stamp come in any order,
and every promise is "before the acting step", whichever order the run has); no integer-part map.

### Points for Roberto

**P30. The split is argued, not machine-checked, on `RStsVariant2`.** The old condition and the conjunction of the two new
ones at `syncDeadline` say the same (the argument under "Before and after"). Default: not proved here (definitions only,
Roberto's word of 28 Oct). Pros: no proof in `Spec/`. Cons: the equivalence rests on a reading of `spec`'s `restart`
case. Alternative: a probe file proving the two directions, as the package's probe did over `RStsVariant`. Pros: the
claim is kernel-checked. Cons: a proof, which was not asked for.

**P31. A message owed nothing has no deadline to say so.** The deadline functions are total, `(m : Msg) → (t : ℝ) → ℝ`, so
every sent envelope is owed by some deadline. Default: kept so; every message is owed (Goldilocks's two kinds of message
cover every object). Pros: the simplest type. Cons: a protocol with a kind of message the network does not promise must
add a filter. Alternative: a filter hypothesis `owed : Envelope Node Msg → Prop` on the two delivery conditions, or
deadlines in `WithTop ℝ`. Pros: says "not owed" directly. Cons: a parameter no current statement needs.

### Taken, tell me to revisit

- **T43. "Up" is outside `crashed` with the local state known**, written out in `Execution.UpBetween` and
  `Execution.UpAndHonestThroughout`; no `Execution.Up` is defined again (D-RSV2-26 (a) removed it). A validator whose
  local state is known is not corrupted, so "up" here implies honest; `UpAndHonestThroughout` writes `x.Honest i p` out
  so that it reads "up and honest". It is version 6's `Execution.Up`. The alternatives were "outside `crashed`" alone
  (would call a validator not yet online up) and "outside `crashed` and outside `adv`" (the same, for the same reason).
- **T44. The three readings sit in `Spec/Conditions.lean`**, in the section "Network", in the namespace `Execution` (so
  that `x.ActingStep k p` reads as the conditions write it), each labelled "a reading of an execution … not part of the
  bare framework". `Spec/Execution.lean` is not edited beyond its docstring.
- **T45. Names.** The deadline instances take `tGST`, `ΔDelay`, `tAsyncStart`, `tAsyncEnd` and `t` (the naming
  conventions: times `t…`, durations `Δ…`, version 6's spelling) where the brief wrote `gst`, `delay`, `b₀`, `b₁`, `σ`.
  The deadline functions are `dl`, `dlW`, `sync` as in the brief, with named binders `(m : Msg) → (tSend : ℝ) → ℝ`,
  `(tRestart : ℝ)`, `(t : ℝ)`. Step indices are `k` (acting), `i` (sending), `j` (delivery), `l` (restart), as the
  replaced definitions had them; nodes `p` and `p'`; the holder's clock reading `tClock`.
- **T46. `SyncedWithinBy` reads the holder's local state and clock by two `some` hypotheses**
  (`x[i][p] = some l`, `x[i].clock p = some tClock`), since both are options in `RStsVariant2`; its content is version
  6's `SyncedWithinBy` over the node reads `nodeReadsOf Pr x` with `serves := Pr.serves`.
- **T47. Only the network's definitions moved.** `NetworkOutside` and `SyncOutside` stay in `probe_04_v6.lean` as
  statement 4's instances (`SyncOutside` now takes `serves`; statement 4 passes `Pr.serves`); `UnforgeableSends`, the two
  adversary bounds and `WeightBounds` stay there too, their "to move once … ruled" notes changed to "stays in this file".
- **T48. Version 6's `NodeObs.serves` is kept**: the protocol's premise `healingConditions` still sees it through
  `phaseSegment`. Version 6's `Execution.ActiveThroughout` and `Execution.Up` are kept; `ActiveThroughout` says what
  `Execution.UpAndHonestThroughout` says.
- **T49. `DueBy`'s docstring calls it part of the conditions `DeliveredBeforeActing` and `CatchUpAfterRestart`**, not a
  condition of its own: it is a property of one envelope at one time, which no statement takes alone.
- **T50. No ruling codes in the new Lean docstrings** (the minimal-docstrings convention); they are in this section and
  in version 6's header.
- **T51. The edits were scripted**: the new section was written to `scratch/rsts2_net/edits/network_section.lean` and
  spliced in by a Python one-off, the probe changed by `scratch/rsts2_net/edits/edit_probe.py`, the three other
  docstrings by Python string replacements; the pages before the edit are in `scratch/rsts2_net/check/`.

## D-NET1 (e), D-NET2 (e), 1 Nov

Roberto, 00:06 IST Sun 1 Nov: "go ahead with the edits in the meantime", on statement 4 expressing the network with memory per
recipient (push plus re-push).

- `Spec/Conditions.lean`, `CatchUpAfterRestart`: the delivery clause reads `∀ (l : Nat) (keep : Bool), j < l → l < k →
  x.lbl l ≠ .restart p keep` in place of `∀ l : Nat, j < l → l < k → x.lbl l ≠ .restart p false`. Read aloud: the delivery comes
  after `p`'s last restart before `k`, whether that restart kept the memory or not. Before, a delivery made before a restart with the
  memory kept counted, although the node may have rejected it (runs M1 and M2 of `experiments/goldilocks/network_facts_review.md`
  section 3.2), so the condition did not give the sync fact. This amends D-ADQ3 (d)'s clause "a restart with the memory kept voids no
  delivery". The same change is made to the trace copy in `experiments/trace-statements/TraceStatements/Environment.lean`.
- No proof reads `CatchUpAfterRestart`. Built: `lake build RStsVariant2 TraceStatements.Statement4 TraceStatements.RStsVariant2Bridge`,
  exit 0, 0 errors, 985 jobs (`scratch/net_n2_check/build.log`).

## D-ST4-34 (e), 3 Nov

Roberto, 22:11 IST Tue 3 Nov: "D-ST4-34 (e)", so that statement 4 over runs (`experiments/la-runs/`) reads its clock and network
conditions through the conditions on executions of this page, one definition per condition, with the meaning it had on the trace.
Measurement: `experiments/goldilocks/laruns_three_trace_conditions.md`. Landing lane `L20261103T1643Z-st4-34e`.

- `Spec/Conditions.lean`, `ClockAdvancesWithinR`: the premise gains `x[i][p] ≠ none` after `p ∉ x[i].crashed`. Read aloud: a
  reading is owed by a node's clock only through a configuration in which the node is up (not crashed, its local state known)
  and not corrupted. Before, a node whose clock had started but which had not yet come online was bound as an up node is; it
  takes no step of its own, so nothing it does could depend on that obligation. The restart consequence is kept: the
  configuration a `restart p keep` enters has `p` outside `crashed`, not corrupted and with its local state known, so the
  condition binds `p` there as before. The docstring's paragraph on a node not yet online is rewritten, and the clause 1 and
  read-aloud texts with it; `Spec/Execution.lean`'s header sentence on the condition likewise.
- `Spec/Conditions.lean`, `DeliveredBeforeActing`, `CatchUpAfterRestart`, `SyncedWithinBy`: each takes
  `(acting : Exec Pr → Nat → Node → Prop)` as its first explicit argument, before the deadline functions (and before `serves`
  for `SyncedWithinBy`), and reads `acting x k p` where it read `x.ActingStep k p`. Nothing else in the three changes.
  `DeliveredBeforeActing Execution.ActingStep dl x` is the condition as it was.
- `Spec/Conditions.lean`, `TickStep`: new reading of an execution beside `Execution.ActingStep`, `x.lbl k = .tick p`. It
  implies `Execution.ActingStep`, not the converse. The network section's header says which readings the parameter takes.
- Users. No definition of this repository applies the three network conditions: Goldfish's `HonestDeliveredBeforeActing` and
  `HonestCatchUpAfterRestart` (`experiments/goldfish-sts/GoldfishSts/Statements/Conditions.lean`) are copies reading
  `x.ActingStep`; their docstrings, which name the framework's forms, now name them with `Execution.ActingStep`. The
  abstract trace layer's `SyncedWithinBy` (`GoldilocksCorrectness.Statements.AbstractTrace`) is another definition.
  Statement 4 over runs takes `ClockAdvancesWithinR`, `DeliveredBeforeActing TickStep (deadlineOutside …)` and
  `CatchUpAfterRestart TickStep (deadlineOutside …) (deadlineOutside …)`.
- Goldfish's proofs that apply `ClockAdvancesWithinR` (through `DiligentWithinR`'s first conjunct) supply the added premise:
  `first_tick` and `block_held_by` from hypotheses they already had, `delivered_after_slot_start` from the window in which the
  validator is up; `clock_ge_of_stamp` and `stamp_succ_le_of_clock` (`GoldfishSts/Proofs/Runs/FrozenSets.lean`) gain the
  hypothesis `x[i][v] ≠ none`, which their callers (`frozen_votes_subset`, `frozen_blocks_subset`) take from `held_vote_sent_by`
  and `held_block_sent_by`. No Goldfish statement changes text.

## Statement 4's asynchronous period as a start and a length, 3 Nov

Roberto, 22:31 IST Tue 3 Nov: "Instead express the period as start and length>=0", then "deltaAsync is a bad name.
AsyncLength". Statement 4 over runs (`experiments/la-runs/LARuns/Statement4OnRuns.lean`) now takes the asynchronous period
as its start `tAsyncStart` and its length `ΔAsyncLength`, followed in the parameter list by
`(hAsyncLength : 0 ≤ ΔAsyncLength)`, and passes `tAsyncStart + ΔAsyncLength` wherever a condition of this page reads the
period's end. Goldilocks's claim (`LARuns/Goldilocks/Instance.lean`) takes the same two parameters. Landing lane: st4
asynchronous period length.

- `Spec/Conditions.lean`, `AsyncPeriod` (`tAsyncStart ≤ tAsyncEnd`, a condition on a statement's parameters): removed. After
  the change nothing in this repository outside `experiments/la-traces/` read it, and `experiments/la-traces/` has its own
  definition, which stays. The page header and the section header of "The asynchronous period, the adversary's weight, the
  healing phase, the committees and the proposers" now name one condition on a statement's parameters,
  `AsyncPeriodEndsInTime`.
- The conditions that take the period's end (`deadlineOutside`, `AsyncPeriodEndsInTime`, `AffectedByAsync`,
  `AsyncPeriodSleepiness`) keep their parameters and their text.
- `scratch/st4_async_length/Equivalence.lean` holds the statement as it was before the change, with a copy of `AsyncPeriod`,
  and proves it equivalent, for every `hAsyncLength : 0 ≤ ΔAsyncLength`, to the statement now at
  `tAsyncEnd := tAsyncStart + ΔAsyncLength`.

## The conditions on executions over `RunReading`, 3 Nov

Each definition of `Spec/Conditions.lean` that reads an execution, except `WeakFair`, `StrongFair` and the structure
`WeightBounds`, is now written once, over any type of execution with a `RunReading`, so that a statement can later take
the conditions on an execution whose configurations carry, for each node, a value of its own type in place of its local
state. Today's name over `Exec Pr` keeps its signature and its docstring and is defined as that definition at the run.
The bare framework (`Spec/Protocol.lean`, `Spec/Execution.lean`) is not changed, and no condition changes meaning:
`scratch/st4_run_reading/same_meaning.lean` proves each name over `Exec Pr` equal to its formula as it was before, over
the run's own readings, by `Iff.rfl`. First landed as twins (each formula written twice, lane
`L20261103T1800Z-st4-run-reading`); written once by the lane `L20261103T1829Z-st4-run-reading-2`, branch
`st4-run-reading`.

- `Spec/RunReading.lean`, new: the class `RunReading X Node Msg L Ev` (the action of each step, the stamps, and in each
  configuration each node's clock, its state of type `L` if known, its view, the sent envelopes, the corrupted set and the
  crashed set), its instance for `Exec Pr` (`L` is `Local Node Msg NodeState`, each reading the run's own), `TraceConfig`,
  `TraceExecution` (configurations, actions and stamps with the three conditions on the real time of `Execution`, and no
  step relation), its instance (`L` is the node's value `V`), `traceOf f x` (the run `x` with each known local state `l`
  replaced by `f l`), and `HonestG`, `InForceG` (`Execution.Honest`, `Execution.InForce` over the class; the two over
  `Exec Pr` stay as they are, in `Spec/Execution.lean`). The class reads a node's state, not only whether it is known,
  because `SyncedWithinBy`, `Execution.InHonestTreeBy` and `Execution.MostOfCommittee` read what the state holds.
- `Spec/Conditions.lean`: 27 definitions over the class, each just before today's name. Names: the name without the
  trailing `R` where it has one (`ClockWithinSkew`, `ClockNotAhead`, `ClockAtTime`, `ClockAdvancesWithin`, `TicksWithin`,
  `DiligentWithin`), the suffix `G` otherwise (`NoCrashDuringG`, `ActingStepG`, `TickStepG`, `UpBetweenG`,
  `UpAndHonestThroughoutG`, `DueByG`, `DeliveredBeforeActingG`, `CatchUpAfterRestartG`, `SyncedWithinByG`,
  `TickOncePerReadingG`, `UnforgeableSendsG`, `InHonestTreeByG`, `HonestSentByG`, `AdversaryUnderIntersectionByG`,
  `AdversaryUnderQuorumByG`, `WeightBoundsG`, `HealingPhaseG`, `MostOfCommitteeG`, `CommitteeSleepinessFromG`,
  `AsyncPeriodSleepinessG`, `HonestProposerThroughG`). 26 of today's names are wrappers, `ClockAdvancesWithinR … x :=
  ClockAdvancesWithin … x`; a parameter that reads a node's memory state `st` (`serves`, `held`, `info`) is passed as
  `fun l => … l.st`. `WeightBounds` keeps its own fields beside `WeightBoundsG`: a definition would have no fields
  `WeightBounds.third`, `WeightBounds.quorum` and no constructor of its own. `WeakFair` and `StrongFair` have no form over
  the class: they read `Execution.Enabled`, the step relation's enabling condition. `syncDeadline`, `deadlineOutside`,
  `AsyncPeriodEndsInTime` and `AffectedByAsync` read no execution and are unchanged.
- `Analysis/RunReading.lean`, new: for each field of the class, a lemma that on a run it is the run's own reading
  (`RunReading.stamp x i = x.stamp i`, …, by `rfl`), in the simp set `runReading_exec` (registered on
  `Analysis/RunReadingSimpAttr.lean`) and in the default simp set; for each name over `Exec Pr`, `…_iff`, that on a run it
  is the definition over the class at the run (by `Iff.rfl`; `weightBounds_iff` field by field); and `…_traceOf`, that
  the definition over the class says on `traceOf f x` what it says on `x`, with a parameter reading a node's state read
  through `f` on the run, and a parameter `acting` taken as two that agree on the trace of `x` and on `x`.
- What callers see. A statement or a call that applies a hypothesis of a condition is unchanged. A proof that takes one
  apart (`rcases hdil.1 … with ⟨j, hj, hj1, hj2⟩`), or proves one through `rw` or `linarith`, sees the class's readings
  (`RunReading.stamp x (j + 1)`) where it expects `x.stamp (j + 1)`; one `dsimp only [RStsVariant2.RunReading.stamp, …]`
  turns them back. 11 such repairs in `GoldfishSts` (`Proofs/Runs/Clocks.lean` 2, `Proofs/Runs/Delivery.lean` 3,
  `Proofs/Runs/FrozenSets.lean` 4, `Proofs/Statement1.lean` 1, `Proofs/Statement3.lean` 1), 5 in each of the four
  equivalence files `scratch/st4_34e/`, `scratch/st4_async_length/`, `scratch/st4_clock_bounds/`, `scratch/st4_nnreal/`;
  none in `LARuns`, `GoldilocksVariant`, `RSts2TraceBridge` or `GoldilocksCorrectness`. Each is a proof line; no statement
  changed. They were placed by `scratch/st4_run_reading/repair_sites.py` from the build's errors and cut to what each
  proof needs by `scratch/st4_run_reading/minimize_repairs.py` (`repairs.tsv` lists every step). After the repairs
  `scratch/st4_nnreal/Equivalence.lean`, the check of statement 4 as it stands, compiles with no error. The other three
  check statement 4's earlier texts against forms it no longer has, and fail only on that (statement 4's later
  arguments, names they read that are gone), none on a reading of the class: `scratch/st4_34e/` and
  `scratch/st4_async_length/` with the errors they had before this change, `scratch/st4_clock_bounds/` since statement
  4's parameters were typed `ℝ≥0`.

## D-C3G3 (a), 4 Nov

Roberto, 00:15 IST Wed 4 Nov: "D-C3G3 (a)". The delivery that `DeliveredBeforeActing` promises comes after the copy's own
sending. Decision text: `experiments/goldilocks/OPEN_DECISIONS.md`, section 3.5 of the re-posed set of 1 Nov. Lane "D-C3G3 (a)
on dev".

- `Spec/Conditions.lean`, `DeliveredBeforeActingG`: the conclusion `∃ j : Nat, j < k ∧ lbl x j = .deliver p e ∧ …` becomes
  `∃ j : Nat, i < j ∧ j < k ∧ lbl x j = .deliver p e ∧ …`. Read aloud: some step after the sending `i` and before the acting
  step `k` delivers `e` to `p`, with no memory-losing restart of `p` between. Before, a delivery of an earlier copy of the same
  envelope, at a step before `i`, counted for the copy sent at `i`; now each copy is owed a delivery of its own. The wrapper
  `DeliveredBeforeActing` follows by its definition. The two docstrings and the network section's header say the delivery
  comes after the sending; the clause 4 note on an earlier copy is replaced by the sentence that it no longer counts.
- `CatchUpAfterRestartG` and `SyncedWithinByG` are unchanged; the ruling names neither. `CatchUpAfterRestartG`'s delivery
  already comes after a restart that comes after the sending. The abstract trace layer's copy in
  `experiments/la-traces/LATraces/Environment.lean` is not changed (statement 4 reads this page's definition since D-ST4-34 (e)).
- Proofs. None needed a repair: the build of `RStsVariant2`, `LARuns`, `GoldilocksVariant`, `RSts2TraceBridge`, `GoldfishSts`
  and `GoldilocksCorrectness` passes with the change alone. No proof of this repository takes the condition apart; Goldfish's
  `HonestDeliveredBeforeActing` is a definition of its own; `deliveredBeforeActingG_traceOf` (`Analysis/RunReading.lean`)
  compiles unchanged.
- Statement 4 and Goldilocks's claim now assume more of the network, so they say less. `scratch/c3g3_dev/Implication.lean`
  holds the condition, statement 4 and Goldilocks's claim as they were at `d316383df`, copied verbatim, and proves that the
  condition now implies the condition then, and that statement 4 then implies statement 4 now and Goldilocks's claim then its
  claim now, for every argument. The converse is not claimed: the two conditions differ on an execution that sends an
  envelope twice to a node that is up throughout, delivers only the first copy, and has the node tick past the second copy's
  deadline.

## The bounds dropped from the first case of `ClockAdvancesWithin`, 4 Nov

Roberto, 01:34 IST Wed 4 Nov: "g072", the action offered after his question whether the clock conditions repeat each other.
Lane GO-72, brief `experiments/goldilocks/briefs/brief_go72_clock_advances.md`.

- `Spec/Conditions.lean`, `ClockAdvancesWithin`: the first case `∃ j : Nat, lbl x j = .setClock p t ∧ (t : ℝ) - ΔClockAhead ≤
  stamp x (j + 1) ∧ stamp x (j + 1) ≤ t + ΔClockBehind` becomes `∃ j : Nat, lbl x j = .setClock p t`. Read aloud: some step
  sets `p`'s clock to `t`. The second case (a crash or a corruption by `t + ΔClockBehind`) is unchanged. The wrapper
  `ClockAdvancesWithinR` follows by its definition. Its docstrings say the first case asks only that the step happen, and that
  `ClockWithinSkewR`, when a statement takes it too, bounds the step's real time; the paragraphs "Consequences" and "A
  consequence at a restart" now say they hold with `ClockWithinSkewR`.
- The parameter `ΔClockAhead` is read nowhere in the formula now. It is kept: dropping it changes the argument lists of
  `ClockAdvancesWithin`, `DiligentWithin` and their wrappers, and so the text of statement 4, Goldilocks's claim and the
  Goldfish statements' `RunConditions` (`experiments/goldfish-sts/GoldfishSts/Statements/Conditions.lean`), which this lane
  edits in proof lines only.
- `Analysis/RunReading.lean`, new kit theorem `clockAdvancesWithin_bounded`: under `ClockWithinSkew`, `ClockAdvancesWithin`
  gives back the case with the bounds (the proof of `scratch/probe_clock_redundancy/Probe.lean`).
- Proofs: five sites of `GoldfishSts` read the bounds and now call the kit theorem (`Proofs/Runs/Clocks.lean`, `first_tick`;
  `Proofs/Runs/FrozenSets.lean`, `clock_ge_of_stamp`, `stamp_succ_le_of_clock` and one site in a later proof;
  `Proofs/Runs/Delivery.lean`, `block_held_by`), each page importing `RStsVariant2.Analysis.RunReading` privately. Three of
  them (`clock_ge_of_stamp`, `stamp_succ_le_of_clock`, `block_held_by`) had no `ClockWithinSkewR` and take it now as the
  hypothesis `hclock`; the two callers of `stamp_succ_le_of_clock` pass `hrc.clock`, the other two have no caller.
- Statement 4 and Goldilocks's claim take `ClockWithinSkew` just before `ClockAdvancesWithin`, so their meaning is unchanged:
  `scratch/go72/Equivalence.lean` copies both, and the formula, as they were at `4b38db01b`, and proves each equivalent to
  its form now for every argument. The abstract trace layer's own `ClockAdvancesWithin`
  (`experiments/la-traces/LATraces/Environment.lean`) is not changed.

## A node's blocks read through the class `BlockTree`, 4 Nov

Roberto, Wed 4 Nov: "go-78", the action offered after his question whether a view's fields could be read without an access
function in statements such as the weight bounds. Lane GO-78, brief `experiments/goldilocks/briefs/brief_go78_block_tree_class.md`.

- `Spec/Conditions.lean`, new class `BlockTree (L : Type) (Block : outParam Type)` with the method `tree : (l : L) → Finset
  Block`: the blocks in the tree of a node whose state is `l`, a reading of an execution's state, not part of the bare
  framework. New instance on `Local Node Msg NodeState` from `[BlockTree NodeState Block]`: the tree of the memory state `l.st`.
- `InHonestTreeByG` and `WeightBoundsG` take `[BlockTree L Block]` in place of their explicit function argument, and read
  `BlockTree.tree l`. The run forms `Execution.InHonestTreeBy` and `WeightBounds` keep their texts and their explicit
  argument; `Execution.InHonestTreeBy` is `InHonestTreeByG` at the run with the local instance `⟨fun l => held l.st⟩`.
- `Analysis/RunReading.lean`: `Execution.inHonestTreeBy_iff` and `weightBounds_iff` are stated under
  `[BlockTree NodeState Block]`, with the run form passed `BlockTree.tree`; `inHonestTreeByG_traceOf` and
  `weightBoundsG_traceOf` take `hf : ∀ l, BlockTree.tree (f l) = BlockTree.tree l.st` (the view map keeps the tree) and
  relate the trace to the run with the same name on both sides.
- `experiments/la-runs/`: the instance `BlockTree (NodeView Block) Block := ⟨NodeView.T⟩` in `Statement4Defs.lean`;
  `HeldByHonestBy` and `WeightBoundsOnViews` removed. Statement 4 writes `WeightBoundsG P.readers.registry tAwakeEnd τ`,
  `RootCollisionBy` writes `InHonestTreeByG τ tBy B`, and Goldilocks's claim writes
  `RStsVariant2.WeightBoundsG (fun _ => goldilocksRegistry) tAwakeEnd τ`.
- No other proof read the two definitions. `scratch/go78/Equivalence.lean` copies both definitions, LARuns's two
  abbreviations, `RootCollisionBy`, statement 4 and Goldilocks's claim as they were at `03cd10195`, and proves each
  equivalent to its form now for every argument.

## The validator set at a block read through the class `BlockRegistry`, 4 Nov

Roberto, Wed 4 Nov: "go79", the action offered after his question whether `P.readers.registry` could be part of what a run
gives, so that statement 4 need not be passed it. Lane GO-79, brief `experiments/goldilocks/briefs/brief_go79_block_registry_class.md`.

- `Spec/Conditions.lean`, new class `BlockRegistry (Block : Type) (Node : outParam Type)` with the method
  `registry : (B : Block) → Registry Node`: the validator set at the block `B`, a reading of a block, not part of the bare
  framework.
- `WeightBoundsG` takes `[BlockRegistry Block Node]` in place of its explicit argument `registry`, and reads
  `BlockRegistry.registry B`. The run form `WeightBounds` keeps its text and its explicit arguments.
- `Analysis/RunReading.lean`: `weightBounds_iff` is stated under `[BlockRegistry Block Node]`, with the run form passed
  `BlockTree.tree` and `BlockRegistry.registry`; `weightBoundsG_traceOf` takes the instance and no `registry`.
- `experiments/la-runs/`: `Vocab` loses its field `registry` (only the weight bounds read it); Goldilocks's blocks get the
  instance `⟨fun _ => goldilocksRegistry⟩` in `Goldilocks/Defs.lean`. Statement 4 takes `[BlockRegistry Block Node]` and
  writes `WeightBoundsG tAwakeEnd τ`; Goldilocks's claim writes `RStsVariant2.WeightBoundsG tAwakeEnd τ`.
- No other proof read `WeightBoundsG` or `Vocab.registry`. `scratch/go79/Equivalence.lean` copies `WeightBoundsG`, `Vocab`,
  `Readers`, the three conclusions, `TracedProtocol`, statement 4 and Goldilocks's vocabulary, readers, traced protocol and
  claim as they were at `ca120f2fd`, and proves: statement 4 then, at any `P`, is statement 4 now at `P` without the field
  and the instance built from `P.readers.registry`; statement 4 now, at any `P` and instance, is statement 4 then at `P`
  with the instance's validator sets as the field; Goldilocks's claim now is its claim then.

## The block and message vocabulary read through classes, 4 Nov

Roberto, Wed 4 Nov: "go80 a", after his question "Can we apply similar treatment to UnforgeableSendsG?". Lane GO-80 (a),
brief `experiments/goldilocks/briefs/brief_go80_vocab_classes.md`.

- `Spec/Conditions.lean`, new class `MessageAuthorship (Msg : Type) (Node : outParam Type)` with the methods
  `author : (m : Msg) → Option Node` and `carries : (m : Msg) → (m' : Msg) → Prop`: who a message's object is attributed
  to and which objects a message includes, a reading of messages, not part of the bare framework.
- `UnforgeableSendsG` takes `[MessageAuthorship Msg Node]` in place of its explicit arguments `author` and `carries`. The
  run form `UnforgeableSends` keeps its text and its explicit arguments, read through a local instance.
- `Analysis/RunReading.lean`: `unforgeableSends_iff` is stated under `[MessageAuthorship Msg Node]`, with the run form
  passed `MessageAuthorship.author` and `MessageAuthorship.carries`; `unforgeableSendsG_traceOf` takes the instance and
  no arguments. Both stay `Iff.rfl`.
- `experiments/la-runs/`: the structure `Vocab` and the trace's field `RealTrace.vocab` are gone, and `Readers` no longer
  extends `Vocab` (it keeps `view`, `committees`, `proposerReqs`). `Statement4Defs.lean` holds two classes:
  `BlockVocab (Block : Type)` with `anc` and `sameRoot` (and the definition `BlockVocab.Compatible`), and
  `MessageVocab (Msg : Type) (Node Block : outParam Type)`, which extends `MessageAuthorship` with `blockOf` and
  `conflicts`. The three conclusions read the classes; statement 4 takes `[BlockVocab Block]` and
  `[MessageVocab Msg Node Block]` and writes `UnforgeableSendsG τ`, `RootCollisionBy τ t`, `ConfirmedPersistsBetween τ …`
  and `FinalizedCompatibleBetween τ …`. Goldilocks's `goldilocksVocab` is replaced by two instances on its blocks and
  objects, in `Goldilocks/Defs.lean`, with the same fields.
- `MessageAuthorship` is in `RStsVariant2` because `UnforgeableSendsG` reads it; the rest is in LARuns, since nothing in
  `RStsVariant2` reads it. `BlockRegistry` stays a class of its own: `WeightBoundsG` reads it and no ancestry.
- No other proof read `UnforgeableSendsG`, `Vocab` or its fields. `scratch/go80/Equivalence.lean` copies
  `UnforgeableSendsG`, `Vocab`, `Readers`, the three conclusions, `TracedProtocol`, statement 4 and Goldilocks's
  vocabulary, readers, traced protocol and claim as they were at `e8a865750`, and proves: statement 4 then, at any `P`, is
  statement 4 now at `P` without the vocabulary and the instances built from `P.readers.toVocab`; statement 4 now, at any
  `P` and instances, is statement 4 then at `P` with the instances' vocabulary; Goldilocks's claim now is its claim then.

## The committees' members read from the execution's state; statement 4 over a protocol and two classes, 4 Nov

Roberto, Wed 4 Nov: "Go81 c", after his question "now, how can w remove readers form CommitteeSleepinessFromG?". Lane
GO-81 (c), brief `experiments/goldilocks/briefs/brief_go81_protocol_classes.md`.

- `Spec/ValidatorSets.lean`, new definition `CommitteeSpec.comap (f : (l : L) → NodeInfo) (committee : CommitteeSpec Node
  NodeInfo) : CommitteeSpec Node L`: the same committee, its members computed from `f l`.
- `Spec/Conditions.lean`: `MostOfCommitteeG`, `CommitteeSleepinessFromG` and `AsyncPeriodSleepinessG` lose their argument
  `info : (l : L) → NodeInfo`; the committees have the type `CommitteeSpec Node L`, their members computed from the state
  the execution records. The run forms `Execution.MostOfCommittee`, `CommitteeSleepinessFrom` and `AsyncPeriodSleepiness`
  lose `info` too: they take committees over the memory state, `CommitteeSpec Node NodeState`, and pass each one through
  `l.st` (`CommitteeSpec.comap fun l => l.st`).
- `Analysis/RunReading.lean`: `Execution.mostOfCommittee_iff`, `committeeSleepinessFrom_iff` and
  `asyncPeriodSleepiness_iff` restated (still `Iff.rfl`); `mostOfCommitteeG_traceOf`, `committeeSleepinessFromG_traceOf`
  and `asyncPeriodSleepinessG_traceOf` restated with each committee on the run read through `f` (`CommitteeSpec.comap f`).
- `experiments/la-runs/`: `Readers` and `TracedProtocol` are gone. `Readers.lean` holds two classes, each a reading of a
  protocol, not part of the bare framework: `NodeViewOf (NodeState : Type) (Block : outParam Type)` with `view`, and
  `ProtocolCommittees (Pr : Protocol Node Msg NodeState Ev) (Block : outParam Type)` with `committees` and
  `proposerReqs : (tAwakeEnd : ℝ) → (π : Exec Pr) → Set (ProposerRequirement Node)`. Statement 4 takes `(Pr : Protocol …)
  [NodeViewOf NodeState Block] [ProtocolCommittees Pr Block]` and writes `traceOf (fun l => NodeViewOf.view l.st) π`,
  `CommitteeSleepinessFromG (ProtocolCommittees.committees π) tGAT τ`, `∀ p ∈ ProtocolCommittees.proposerReqs tAwakeEnd π`
  and `AsyncPeriodSleepinessG (ProtocolCommittees.committees π) …`. `toRealTrace` takes `tAwakeEnd` and the run, and the
  theorems about it in `Proofs.lean` take `tAwakeEnd` in place of the readers. Goldilocks's `goldilocksReaders` and
  `goldilocksTracedProtocol` are replaced by two instances in `Goldilocks/Instance.lean`, with the same fields.
- The two classes are in LARuns: they read LARuns's `NodeView`, `CommitteeSpec` and `ProposerRequirement`, and nothing in
  `RStsVariant2` reads them. `Readers.held` had no reader and is gone.
- No other proof read the three conditions or `Readers`. `scratch/go81/Equivalence.lean` copies the three conditions,
  `Readers`, `TracedProtocol`, statement 4 and Goldilocks's readers, traced protocol and claim as they were at
  `98f203173`, and proves: each committee condition then, at any `info`, is the condition now at the committees read
  through `info`, and the condition now is the condition then at `id`; statement 4 then, at any `P`, is statement 4 now at
  `P.protocol` with the instances built from `P.readers`; statement 4 now, at any `Pr` and instances, is statement 4 then
  at the readers built from the instances at the `tAwakeEnd` it is applied at; Goldilocks's claim now is its claim then.

## The classes read by the conditions on executions renamed, 4 Nov

Roberto, Wed 4 Nov, D-ST4-38 (a′): `RunReading` is `AbstractExecution` and `CommitteeReading` is `AbstractExecutionWithCommittees` (pages `Spec/AbstractExecution.lean`, `Analysis/AbstractExecution.lean`, `Analysis/AbstractExecutionSimpAttr.lean`, the simp set `abstractExecution_exec`, the lemmas `abstractExecution_…_exec`), with the two docstrings rewritten to say what is abstract; no definition changed (script `scratch/st4_rename_abstract_execution/rename.py`).

## The trace renamed `ObservedRun`, 4 Nov

Roberto, Wed 4 Nov, D-ST4-39 (e): `TraceExecution` is `ObservedRun`, `traceOf` is `observe` (the lemmas `…_traceOf` are `…_observe`), and in LARuns `ProtocolTrace` is `ObservedRunWithCommittees`, `protocolTraceOf` is `observeWithCommittees`, its field `exec` is `run`; `TraceConfig` keeps its name; the docstrings of `AbstractExecution`, `ObservedRun`, `ObservedRunWithCommittees`, `observe` and `observeWithCommittees` open with plain first sentences; no definition changed (scripts `scratch/st4_rename_observed_run/rename.py`, `prose_rsts2.py`, `prose_laruns.py`, `prose_hand.py`).

## The class read by the conditions renamed `Observable`, 4 Nov

Roberto, Wed 4 Nov, D-ST4-47 (d), replacing D-ST4-38 (a′): `AbstractExecution` is `Observable` and `AbstractExecutionWithCommittees` is `ObservableWithCommittees` (pages `Spec/Observable.lean`, `Analysis/Observable.lean`, `Analysis/ObservableSimpAttr.lean`, the simp set `observable_exec`, the lemmas `observable_…_exec`, the projection `toObservable`); the class's first sentence ends "Runs and observed runs are observable.", `ObservedRun`'s "It is `Observable`."; no definition changed (script `scratch/st4_rename_observable/rename.py`).

## `ActsWithinSkew`, a new condition on executions, 5 Nov

T-B4-2 of `experiments/goldilocks/route_b_B4_B5_plan.md` (section 5.2), taken by the coordinator under Roberto's delegation of 5 Nov 04:20 IST; lane B4-0. `Spec/Conditions.lean`: `ActsWithinSkewG ΔClockBehind x` over any `Observable`, beside `TicksWithin`: every tick and every restart a node takes while its clock reads `t` is at a real time at most `t + ΔClockBehind`; its run form `ActsWithinSkew`, defined as `ActsWithinSkewG` at the run. `Analysis/Observable.lean`: `actsWithinSkew_iff` and `actsWithinSkewG_observe`, both by `Iff.rfl`. No other definition changed; no statement reads it yet.

## `SyncedWithinByG` reads its receiver up to its acting step, and has two clauses more, 5 Nov

Roberto's rulings D-B1R7 (g′) and D-B1R19 (a), applied in the form over any `Observable` with the parameter `acting` (lane B4-1b, `experiments/goldilocks/route_b_B4_B5_plan.md`). `Spec/Conditions.lean`: a new reading `UpAndHonestUntilActingG acting x t t' p` (the node up and honest in every configuration left at `t` or later, up to the one its first `acting` step at a real time at least `t'` starts from) and its run form `Execution.UpAndHonestUntilActing`; `SyncedWithinByG` takes its receiver through `UpAndHonestUntilActingG acting x t (sync m t) p'` in place of `UpAndHonestThroughoutG`, concludes either that the receiver already serves `m` in the configuration in force at `t` or the delivery as before, and adds that the receiver stays up and honest from the delivery's configuration up to that acting step; `SyncedWithinBy` is still `SyncedWithinByG` at the run. `Analysis/Observable.lean`: `Execution.upAndHonestUntilActing_iff` by `Iff.rfl`, `upAndHonestUntilActingG_observe`, and `syncedWithinByG_observe` repaired for the two disjuncts. No statement of LARuns reads `SyncedWithinByG`.

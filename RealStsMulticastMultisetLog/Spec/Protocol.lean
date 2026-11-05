module
public import Mathlib.Data.Set.Image
public import RealStsMulticastMultisetLog.Spec.Message

@[expose] public section

/-!
# Protocols and the system they induce — the specification

Definitions only. The theorems about them — what each helper does to each field, the two
eliminators, and what a `NodeStep` may and may not touch — belong to an analysis library
beside this one (the framework's are in `deps/lean-sts/StsMultisetLog/Analysis/Lemmas.lean`),
so that reading the model does not mean reading its proofs.

One proof stays here, because a *definition* needs it: `nodeStep_total`, which discharges
`ActionSpec.feasible` inside `nodeSpec` (after a short proof, in place, that the configuration a
node action starts its reaction from still has the node's local state known); the `feasible` of
`crashDuring` is proved in place, the same way, and the `feasible` of `deliverSpec` by cases on
whether the validator is corrupted, from `nodeSpec`'s. That obligation is why the split cannot be
perfectly clean. No other theorem is on this page.

The framework this is copied from had a function `extract`, reading a reaction back out of
the configurations before and after it, and two more proofs: `extract`'s round trip with
`applyNodeStepResult`, and `nodeStep_iff_exists`, the equivalence of its quantifier-free
`NodeStep` with the existential one. All three are gone: a reaction's effects now include disk writes, which the framework's own
write at the end of the step overwrites, and their order relative to the sends, which the
configurations do not record; so a reaction is no longer a function of the two
configurations, and `NodeStep` is the existential.

## Every declaration states its own parameters

No `variable` command is used: each declaration writes every parameter it depends on in its own signature, so that a
reader sees all of a definition's parameters where it is written (Roberto, 2026-10-29: "remove implicit variables from the
rstsvariatn2 spec. it is much harder to read for me"). The binders keep the kinds and the order the section variables of
`RStsVariant` gave them, so that every use reads as before.

A protocol reacts to **events**, and to nothing else. The framework generates
exactly the events it knows about — `tick` (the timer interrupt, at the validator's current clock
reading) and `recv m` (a message was delivered, and is already in the view) — while every other
trigger goes through `custom`, whose type `Ev` is the protocol's own, conditioned on
`Protocol.enabled`. A restart is no event: it is a pure change of the node's state, made by
the protocol's routine `Protocol.restart`, and no reaction runs at it. A clock change is no event
either: `setClock` changes the reading and runs no protocol code.

## Real time is the execution's; the clock advances by a step of its own

This copy is the real-time form of the variant `StsVariant` (D-SVF7 (H)). A configuration carries
no time and no step reads one: the real time at which each configuration of a run is entered is a
field of the execution, `Execution.stamp` (D-DNS1 (a); `RealStsMulticastMultisetLog.Spec.Execution`). There is one
step relation, `spec`, and no step moves a time.

* **`setClock p t` sets `p`'s clock to the reading `t` and runs no protocol code.** `p`'s clock is
  `c.clock p`, `some` reading while the clock exists and `none` otherwise. The step is enabled only
  at a validator that is not corrupted, `p ∉ c.adv`. Once the clock exists, the step is enabled
  when `t` is greater than the current reading, whether `p` is up or crashed. Before it exists, the
  step starts it at any reading, before or after `p` has come online (see "Unknown local state").
  The clock is the node's hardware: it advances while the node is crashed. `corrupt p` empties it,
  and since `setClock` is not enabled at a corrupted validator, a corrupted validator has no clock
  from then on. No other step changes it. So while a node is not corrupted its clock strictly
  increases along a run, and is never set back. The step happens at a real time, the stamp the
  execution gives it, of its own for each node: the clocks are digital, the steps that set them
  are not.
* **`tick p` is the timer interrupt.** It runs `p`'s tick reaction at `p`'s clock reading, and
  changes no clock. It is enabled when `p` is up and honest, with its local state known and its
  clock existing. The step relation does not limit the
  number of ticks at one reading: a protocol whose tick reaction must run once per reading keeps in
  its state the last reading it reacted to. Which ticks a run must contain, and by when, is a
  fairness condition on executions (`TicksWithinR`, `RealStsMulticastMultisetLog.Spec.Conditions`).
* **`deliver p e` and `custom p ev` run their reactions at `p`'s clock reading**, and change no
  clock. The framework does not order a delivery and a tick at one reading (`Action.deliver`). A
  `deliver p e` at a corrupted `p` runs no reaction and reads no clock (section "Views").
* **`restart p keep` needs the clock and changes no clock.** It is enabled only when `p`'s clock
  exists. The restarted node's state is rebuilt by `Protocol.restart`, which is handed the reading
  its clock holds then. So a node restarted while its clock reads `t` may then tick at `t`.
* **What relates a reading `t` to the real time is a separate condition on executions, not part
  of the step.** `ClockWithinSkewR ΔClockAhead ΔClockBehind` (`RealStsMulticastMultisetLog.Spec.Conditions`)
  says every `setClock p t` is taken at a real time in `[t − ΔClockAhead, t + ΔClockBehind]` (D-DNS2 (a)); one shared clock is
  its instance `ΔClockAhead = ΔClockBehind = 0`. Nothing in `spec` chooses the bounds.

## What differs from `RStsVariant`, and why

In `RStsVariant` (`experiments/r-sts-variant/RStsVariant/Spec/Protocol.lean`), `tick p t` both set
`p`'s clock to `t` and ran the tick reaction, and was enabled only when `c[p].clock < t`; and
`restart p t keep` set the clock to `t`. So a node restarted with the reading `t` could not tick
at `t`. Here the clock advances by an environment step of its own, `setClock`, which runs no
protocol code; `tick` and `restart` lose their reading argument and read the stored clock; and the
clock runs while the node is crashed. This is the shape the literature uses for real time with
clocks: time, or a clock, advances by steps that change nothing else, and the protocol's steps read
it (Abadi and Lamport 1994, Lamport's real-time TLA+, timed I/O automata, the hardware clocks of
Attiya and Welch), and the hardware clock of Cristian and Fetzer 1999 runs through a process crash.
The survey is `experiments/sts-variant/step_model_literature.md`; every change is listed in
`experiments/r-sts-variant-2/CHANGES.md`.

A second change, of 29 Oct 2026: a validator's local state may be
unknown, and its clock may not exist yet, as the section "Unknown local state" says. The clock
left `Local` for a configuration field of its own, `Config.clock`, so that it can go on existing
while the local state is unknown. `CHANGES.md`, section "Unknown `Local`, 29 Oct", lists the
changes and the points left open.

A third change, also of 29 Oct 2026: a restart needs the clock. `restart p keep` is enabled only
when `p`'s clock exists, and `setClock` may start a clock before its validator comes online. So a
validator is never online without a clock, and `Protocol.restart` is always handed a reading.
`CHANGES.md`, section "A restart needs the clock, 29 Oct", lists the changes.

A fourth change, also of 29 Oct 2026: nothing is kept for a corrupted validator. `corrupt p` empties
`p`'s clock as well as its local state, and `setClock p t` is enabled only when `p` is not
corrupted. `CHANGES.md`, section "D-RSV2-2 (b) and D-RSV2-12 (b), 29 Oct", lists the changes.

A fifth change, also of 29 Oct 2026: the view left `Local` for a configuration field of its own,
`Config.view`, so that every validator has a view in every configuration, and a delivery to a
corrupted validator is a step, which files the message into its view, as the section "Views" says.
`CHANGES.md`, section "The view leaves `Local`, 29 Oct", lists the changes and the points left open.

## Unknown local state

A validator's local state (`Local`: its memory and its disk) is **known** or
**unknown**: `c[p]` is `some l` or `none`. It is unknown before the validator first comes
online, and from the moment the validator is corrupted on. A crashed validator keeps its local
state: its disk, and its memory when the restart keeps it, are what its restart reads.

* Every validator starts with an unknown local state and no clock (`Init`).
* The first `setClock p t` starts `p`'s clock at the reading `t`, before `p` has come online or
  after, provided `p` is not corrupted.
* `restart p keep` needs `p`'s clock to exist. At a validator whose local state is unknown and
  that is not corrupted, it brings the validator online: its local state becomes
  `Pr.initialLocal p t`, `t` its clock reading (its initial state at `t` in memory, its persistent
  part on disk), whatever `keep`; its view is not touched. So a validator's clock has started before it first comes
  online, and a validator whose local state is known always has a clock.
* `corrupt p` sets `p`'s local state to `none` and `p`'s clock to `none`. No step sets either
  again: `restart` and `setClock` are not enabled at a corrupted validator.
* `tick`, `custom` and `crashDuring`, and a `deliver` to an honest validator, are enabled only at
  a validator whose local state is known (and that is up and honest); they run at its clock
  reading. A `deliver` to a corrupted validator runs no reaction (section "Views").

A validator is **down** when it is in `Config.crashed`, or when its local state is unknown and it
is not corrupted (it has never come online); **up** otherwise.

## Views

Every validator has a **view**, `c.view p`: the set of signed messages delivered to it so far. The
view is not part of the local state: it is a configuration field of its own, `Config.view`, which
holds a set for every validator in every configuration, whether its local state is known or not.

* Every view starts empty (`Init`).
* A delivery `deliver p e` files `e`'s signed message into `p`'s view, and only a delivery does.
* At an honest validator, the delivery is enabled when `p` is up, with its local state known and
  its clock existing, as for its other reactions; the reaction to the message then runs at its
  clock reading (`nodeSpec`).
* At a corrupted validator, the delivery is enabled whenever `e` is on the wire and names `p` among
  its recipients, whether `p` is crashed or not; it files the message into the view and runs no
  protocol code, since a corrupted validator has no local state (`deliverSpec`).
* No other step changes a view: a crash, a restart, a corruption and a change of the clock leave
  it as it was.

So the view of a corrupted validator goes on recording what the network delivers to it. The view
is the environment's account of what was delivered: no reaction reads it (`Protocol.step`), and
neither does the adversary's step `adversarial`.

## The environment is state

A node is **up** or **down**, as the section "Unknown local state" says: down when it is in
`Config.crashed` or has never come online. Who
is corrupted and who is crashed are fields of the configuration, `Config.adv` and
`Config.crashed`, and the environment changes them by steps of the run: `corrupt p` puts
`p` in `adv` for good, `crash p` puts it in `crashed`, `restart p keep` takes it out.
Every enabling condition reads these two fields and the configuration's other fields, and
nothing else: no time. The framework this is copied from has the environment as a `Schedule`,
functions of the time fixed for the whole execution. Here the environment's steps are steps of the
run, so each comes at whatever real time the execution's stamp gives it: a corruption, a crash or a
restart at any real time.

Whether a node's network is cut is in neither the configuration nor the conditions on executions:
the integer variant's schedule `Off` is not carried (D-SVF6 (c)). A model that needs a cut network
states a condition of its own.

## Multicast

A send names its recipients: every validator (`Recipients.all`, a broadcast) or a chosen
set (`Recipients.only`). A reaction's sends are `Addressed` messages; the log holds
`Envelope`s, signed and addressed; a delivery `deliver p e` requires `p` among `e`'s
recipients and hands `p` the signed message without the recipients. The adversary
(`adversarial`) chooses its recipients in the label. A relay is no action of its own: a
protocol that relays does so in its reactions, addressing the relayed message as it
chooses. A protocol that only broadcasts addresses every send to `.all`.

## Memory, disk, and the effects of a reaction

A validator's known local state `l` (`c[p] = some l`) holds two node states: its memory, `l.st`,
and its disk, `l.disk`. The disk holds the persistent part of a state, and which part that is is
the protocol's to say, through its routine `Protocol.persist`. When the validator comes online,
its disk is `Pr.persist` of its initial state.

A reaction returns the validator's new memory state and an ordered list of effects
(`NodeEffect`), each a send (an addressed message put on the wire, signed by the reacting
validator) or a write (the disk set to a given state), in the order the protocol performs
them. A protocol writes explicitly where the order of writing and sending matters: a record
that must be on disk before a send that depends on it is written by a `write` placed before
that `send`.

A **completed** reaction (a `tick`, `deliver` or `custom` step) applies the whole list in
order, sets the memory to the new state, and then the framework writes `Pr.persist` of the
new state to the disk. So after every completed step the disk holds the persistent part of
the state that step left, whatever the protocol wrote during it.

## Crash and restart

The environment crashes a validator in one of two ways, and either way it joins `crashed`,
so from then on, while it is honest, it does nothing and receives nothing.

* `crash p`, **between steps**: the validator's local state is untouched, so its disk is
  `Pr.persist` of the state its last completed step left.
* `crashDuring p a k`, **during a reaction**: `a` is the node action interrupted (a tick, a
  delivery or a protocol event, a `NodeAction`), enabled when `a`'s own step is. The reaction
  `a` would run runs; only its first `k` effects are applied (its sends go on the wire, its
  writes set the disk); the framework's final write is skipped and the new memory state is
  discarded. A `k` at or past the length of the list applies every effect, and still skips
  the final write. So a crash between a send and a disk write is a step of a run, which is
  the case a record written before a signed send exists to survive.

The environment restarts a crashed honest validator whose local state is known by
`restart p keep`, which needs its clock to exist (a validator whose local state is known always
has one): it leaves `crashed`, its clock is unchanged, and its node state is rebuilt by the
protocol's routine `Protocol.restart`, at the reading `t` its clock holds. (The same step at a
validator whose local state is unknown brings it online: section "Unknown local state" and
`spec`.) `keep` says whether the node's memory survived: with
`keep = false`, a reboot, the new state is `Pr.restart t false` of the **disk**; with
`keep = true`, a return with memory intact, as after a pause of the process, it is
`Pr.restart t true` of the **memory**. After a `crashDuring`, the memory is the state held before the interrupted
reaction, since its new state was discarded. The disk is kept in both cases, and the view,
a configuration field of its own (`Config.view`), is not touched by a restart.
The view is the record of every message delivered to the validator, which the environment
reads to say what the network has done; what the validator itself kept of those messages is
in its node state. No reaction runs at the restart: the node's first reaction afterwards is
its next tick, delivery or `custom` event. Since the view is kept, a promise that a restarted
validator receives a message again is stated over the delivery steps after its last restart
with `keep = false`, not over its view (the conditions on executions `DeliveredBeforeActing` and
`CatchUpAfterRestart`, `RealStsMulticastMultisetLog.Spec.Conditions`).

A model whose reactions are atomic assumes `NoCrashDuring` (`RealStsMulticastMultisetLog.Spec.Conditions`): no
step is a `crashDuring`, so every crash finds the disk holding `Pr.persist` of the state the last
step left.

Two facts the framework had to assume of a schedule hold here by construction: corruption
is permanent (`corrupt` only inserts), and a crashed honest node acts and receives nothing
(`tick`, `custom` and `crashDuring`, and `deliver` at an honest node, require their node outside
`crashed`, with its local state known and its clock existing; its clock still advances by
`setClock`), and a corrupted validator keeps nothing but its view (`corrupt` empties its local
state and its clock, and neither `restart` nor `setClock` is enabled at it; deliveries go on
filing messages into its view). Timing conditions are
predicates on executions (`RealStsMulticastMultisetLog.Spec.Conditions`), so different models impose
different ones over the same step relation.
-/

set_option autoImplicit false

universe u v

namespace Framework.RealStsMulticastMultisetLog

/-- What a protocol reacts to. `Ev` is the protocol's own event type; use `Empty`
    if it has none. -/
inductive Event (Node Msg Ev : Type) where
  /-- The timer interrupt, at this validator's current clock reading. -/
  | tick
  /-- A message was delivered; it is already in the view. -/
  | recv (m : SignedMsg Node Msg)
  /-- A protocol-specific event — a timer firing, say. -/
  | custom (ev : Ev)

/-- One effect of a node's reaction on the world outside its memory: a send, or a write to its
    disk.

    Named `NodeEffect` rather than `Effect`, which in this file means an *action's* effect on
    the whole configuration (`ActionSpec.Effect`); the two live at different levels. -/
inductive NodeEffect (Node Msg NodeState : Type) where
  /-- Put the addressed message `a` on the wire, signed by the reacting validator when
      applied; the network decides when each recipient receives it. -/
  | send (a : Addressed Node Msg)
  /-- Set the validator's disk to `d`. A protocol writes the persistent part of a state,
      typically `persist s` for the state `s` it has reached at that point of the reaction. -/
  | write (d : NodeState)

/-- What one node's step produces: its new memory state, and its effects in the order the
    protocol performs them.

    A completed step applies the effects in order, sets the memory to `state`, and then the
    framework writes `persist state` to the disk (`applyNodeStepResult`); a step interrupted
    by a crash applies only a prefix of the effects (`applyCrashDuring`). The order is what a
    protocol uses where writing before sending matters: a record written to disk before a
    send that depends on it survives any crash that the send survives. A protocol with
    nothing to write in the middle of a reaction lists its sends only, and the final write
    keeps the disk up to date.

    Named for what it is rather than `Effect`, which in this file means an *action's*
    effect on the whole configuration (`ActionSpec.Effect`). -/
structure NodeStepResult (Node NodeState Msg : Type) where
  /-- The node's memory state afterwards. -/
  state : NodeState
  /-- The sends and disk writes, in the order performed. A protocol that only broadcasts
      addresses every send to `.all`. Sending `m` twice in one reaction puts two copies on
      the wire, as `Config.sent` counts copies; since views are `Finset`s no validator can
      tell. -/
  effects : List (NodeEffect Node Msg NodeState)

/-- A protocol. -/
structure Protocol (Node Msg NodeState Ev : Type) where
  /-- `init r p`: the state the validator `p` starts with when it comes online, given its clock
      reading `r` at that moment. Read once per validator, by the `restart` that brings it online
      (`Protocol.initialLocal`); `Init` sets no state. A protocol whose start does not depend on
      the time ignores `r`; one that tells a validator online from the start from one that joins
      later reads it (D-PHC8 (d), 29 Oct 2026).

      Read aloud: the state `p` starts with when it comes online at the reading `r`. -/
  init : Time → Node → NodeState
  /-- `step p r s e res` — `res` is *a* reaction `p` may have to `e`, where `r`
      is **`p`'s own clock reading**, not the real time.

      The reaction sees `p`'s clock reading, its memory state `s` and the event `e`, and
      never the view. A protocol must not read what a restart without memory would take
      from it, and the view survives such a restart while the memory does not. A delivered
      message reaches the reaction through the event `recv m`; what the validator keeps of
      it is in its memory state. The view is the environment's account of what the network
      has delivered, read by the execution's conditions, not by the protocol.

      A relation, not a function, so honest behaviour may be underspecified: which
      payload a leader proposes, which of several equally valid chains it follows,
      anything a specification leaves open. A protocol that is in fact deterministic
      lifts its function with `step p r s e res := res = f p r s e`, which keeps
      it computable — see the examples. -/
  step : Node → Time → NodeState → Event Node Msg Ev →
    NodeStepResult Node NodeState Msg → Prop
  /-- Some reaction is always available: a protocol may not get stuck. This is what
      discharges each action's `feasible`, so it is the protocol-side counterpart of
      Event-B's FIS. -/
  total : ∀ p r s e, ∃ res, step p r s e res
  /-- When a protocol-specific event may fire, also against the local clock. -/
  enabled : Time → NodeState → Ev → Prop
  /-- `persist s`: the part of the state `s` that lives on disk. The framework writes
      `persist` of the new state to the disk after every completed reaction, and the initial
      disk is `persist` of the initial state. A protocol with nothing in memory writes
      `persist s := s`. -/
  persist : NodeState → NodeState
  /-- `restart r keep s`: given the boot reading `r` and whether the node's memory survived
      (`keep`), the node state a validator holds after a restart. A pure change of state: it
      sends nothing and runs no reaction.

      With `keep = false` the memory is lost and `s` is the validator's **disk**: what the
      framework's last write or the protocol's last `write` left there. The result is the
      state rebuilt from it, with what was held in memory at its initial value. A protocol
      whose disk holds the whole state writes `restart _ false d := d`; one with nothing on
      disk `restart r false _ := init r p` for the validator at hand. With `keep = true` the
      memory survived, as when the process was only paused, and `s` is the validator's
      **memory**: a protocol that loses nothing then writes `restart _ true s := s`, or
      keeps the reading `r` in `s`. The reading `r` is the validator's clock reading at the
      restart, which the restart does not change; a protocol that does not read the time at a
      restart ignores it.

      Called only for a validator whose local state is known; a restart is enabled only when the
      validator's clock exists, so `r` is always its reading. A restart of a validator whose local
      state is unknown (it has never come online; a corrupted validator is not restarted) does not
      call it: the validator's state is then built from `init` at the reading `r`
      (`Protocol.initialLocal`). -/
  restart : Time → Bool → NodeState → NodeState

/-- What a validator holds locally: one structure rather than several parallel
    maps, so an action names the one field it changes and adding per-validator
    state touches one place.

    The validator's clock is not in it: the clock is the validator's hardware, and it goes on
    existing when the local state is unknown (`Config.clock`). Its view is not in it either: every
    validator has a view in every configuration, a corrupted one included (`Config.view`). -/
structure Local (Node Msg NodeState : Type) where
  /-- Its protocol state in memory. -/
  st : NodeState
  /-- Its disk: the persistent part of a state, set by the protocol's `write` effects and by
      the framework's write of `persist` of the new state after every completed reaction.
      A restart that loses the memory rebuilds the state from it. -/
  disk : NodeState

/-- `Pr.initialLocal p t`: the local state the validator `p` is given when it comes online with an
    unknown local state at the clock reading `t`, by a `restart` (`spec`): its memory is its initial
    state `Pr.init t p`, its disk the persistent part of that state. Its view is not part of it
    (`Config.view`), and the restart leaves the view as it was.

    Read aloud: `p`'s initial state at the reading `t` in memory, its persistent part on disk. -/
def Protocol.initialLocal {Node Msg NodeState Ev : Type} (Pr : Protocol Node Msg NodeState Ev)
    (p : Node) (t : Time) : Local Node Msg NodeState :=
  { st := Pr.init t p, disk := Pr.persist (Pr.init t p) }

/-- A global configuration. It carries no time: the real time at which a configuration of a run
    is entered is the execution's (`Execution.stamp`).

    Read aloud: every validator's local state, known or not, every validator's clock reading, if
    its clock exists, every validator's view, every envelope ever put on the wire, the corrupted
    validators and the crashed ones. -/
structure Config (Node Msg NodeState : Type) where
  /-- Each validator's local state: `some l` when it is known, `none` when it is unknown.

      It is unknown before the validator first comes online and from the moment it is corrupted
      on: every validator starts with `none` (`Init`), `corrupt p` sets `p`'s to `none`, and a
      `restart` of a validator whose local state is `none` gives it `Pr.initialLocal p t`, `t` its
      clock reading. A crash
      leaves it as it is: a crashed validator keeps its memory and its disk, which its restart
      reads. The view is not part of it (`view`). A validator whose local state is unknown takes
      no step that runs its reaction (`nodeSpec`). -/
  nodes : Node → Option (Local Node Msg NodeState)
  /-- Each validator's clock reading: `some t` while its clock exists, `none` otherwise: before it
      starts, and from the moment the validator is corrupted on.

      The clock is the validator's hardware. Every validator starts with `none` (`Init`). The first
      `setClock p t` starts it at the reading `t`, before or after `p` first comes online; each
      later one sets it to a greater reading: it advances while `p` is crashed, and a restart leaves
      it as it is. `setClock` is enabled only while `p` is not corrupted. `corrupt p` sets it to
      `none`, and since `p` stays corrupted, no step sets it again. No other step changes it. A
      restart is enabled only once it exists, so a validator comes online only after its clock has
      started. Every reaction of the validator, and its restart, runs at this reading. -/
  clock : Node → Option Time
  /-- Each validator's view: the set of signed messages delivered to it so far. Every validator
      has one in every configuration, whether its local state is known or unknown, corrupted
      validators included.

      Every view starts empty (`Init`). A delivery `deliver p e` inserts `e`'s signed message
      into `p`'s view, at an honest `p` before its reaction runs and at a corrupted `p` with no
      reaction; no other step changes it, so a crash, a restart and a corruption leave it as it
      was. It only grows. No reaction reads it (`Protocol.step`): it is the environment's account
      of what the network has delivered, read by the conditions on executions. -/
  view : Node → View Node Msg
  /-- Every message ever put on the wire, each with its recipients, **with multiplicity**.
      Monotone.

      A multiset rather than a set: `∪` is lossy, so a reaction that re-sends a message
      already in the log would leave no trace, and the envelopes a step put on the wire are
      `post.sent - pre.sent` (what `DueBy` reads, part of the conditions on executions
      `DeliveredBeforeActing` and `CatchUpAfterRestart`, `RealStsMulticastMultisetLog.Spec.Conditions`). In the
      framework this is copied
      from, that also made a reaction a function of the configurations before and after it;
      with disk writes among a reaction's effects it no longer is, and `NodeStep` is an
      existential.

      The price is that multiplicity is observable state: two executions differing only in
      how many times a message was sent are different configurations. Nothing stated in
      this framework can tell them apart, since every property is membership-based, but the
      model does distinguish more than the protocol semantics needs. It also makes `sent`
      finite by typing, which reachable configurations were anyway. -/
  sent : Multiset (Envelope Node Msg)
  /-- The validators corrupted so far. Grown by `corrupt` and shrunk by nothing, so
      corruption is permanent by construction. `tick` and `custom` are enabled only at a
      validator outside it, and `adversarial` only at a validator in it; `deliver` is enabled at
      both, and at a validator in it files the message into its view and runs no reaction. A
      corrupted validator's local state is unknown (`nodes`), and no `restart` gives it one; it
      has no clock (`clock`), and no `setClock` gives it one; its view (`view`) is kept, and
      deliveries go on growing it. -/
  adv : Finset Node
  /-- The validators crashed and not yet restarted. A validator is **down** when it is in this
      set, or when its local state is unknown and it is not corrupted (it has never come online);
      it is **up** otherwise. A validator that has never come online is not in this set unless
      a `crash` step put it there. A
      validator joins it by `crash`, or by `crashDuring` (a crash during one of its
      reactions), and leaves it by `restart` alone; while in it, an honest validator does
      nothing and receives nothing: `tick`, `custom` and `crashDuring`, and `deliver` at an honest
      validator, require their validator outside this set. A corrupted validator in it is still
      delivered messages into its view. Its clock, once it exists, still advances (`setClock`),
      unless the validator is corrupted. -/
  crashed : Finset Node

/-- `c[p]` is `p`'s local state, `some l` when it is known and `none` when it is unknown
    (`Config.nodes`). Indexing is total, hence the trivial side-condition. -/
instance {Node Msg NodeState : Type} :
    GetElem (Config Node Msg NodeState) Node (Option (Local Node Msg NodeState))
      (fun _ _ => True) where
  getElem c p _ := c.nodes p

/-- A node action: one of the three actions that run a reaction of the node, named without the
    node. It is what `Action.crashDuring` names as the reaction a crash interrupts. Each runs at
    the node's current clock reading, and none changes the clock. -/
inductive NodeAction (Node Msg Ev : Type) where
  /-- The timer interrupt: the node reacts at its current clock reading. -/
  | tick
  /-- The envelope `e` is delivered to the node, which reacts to its signed message. -/
  | deliver (e : Envelope Node Msg)
  /-- A protocol-specific event fires at the node. -/
  | custom (ev : Ev)

/-- Transition labels: the environment's (`setClock`, `corrupt`, `crash`, `crashDuring`,
    `restart`), the adversary's (`adversarial`), and the nodes' (`tick`, `deliver`, `custom`), each
    of the last running a reaction only at a node outside `crashed` and outside `adv`; a `deliver`
    at a node in `adv` files the delivered message into the node's view and runs no reaction. No
    label moves a time: the real time of each step is the execution's stamp.

    Read aloud: a step is a change of a node's clock, a node's tick, delivery or event, an
    environment's corruption, crash (between steps or during a reaction) or restart, or an
    adversarial send. -/
inductive Action (Node Msg Ev : Type) where
  /-- The environment sets the clock of the validator `p`, not corrupted, to the reading `t`:
      greater than its current one, whether `p` is up or crashed, once the clock exists; any
      reading, to start the clock, when `p`'s clock does not exist yet, before or after `p` has
      come online. Not enabled at a corrupted validator. No protocol code runs. -/
  | setClock (p : Node) (t : Time)
  /-- The timer interrupt at `p`: `p` reacts at its current clock reading. -/
  | tick (p : Node)
  /-- The envelope `e`, which names `p` among its recipients, is delivered to `p`, which
      reacts to its signed message at its current clock reading.

      The framework does not order a delivery and a tick at one reading: after `p`'s clock comes
      to read `t`, a delivery may come before `p`'s tick at `t`. A protocol whose reaction to a
      delivery must follow its reaction to the current reading runs the latter first in its own
      handler of `recv`, which sees the reading and can compare it with the last reading the
      state has reacted to.

      At a corrupted `p`, crashed or not, the delivery files `e`'s signed message into `p`'s view
      and runs no reaction: a corrupted validator has no local state and no clock. -/
  | deliver (p : Node) (e : Envelope Node Msg)
  /-- The environment corrupts `p`: `p` joins `adv` for good, its local state becomes unknown,
      and its clock is emptied. Its view is kept. -/
  | corrupt (p : Node)
  /-- The environment crashes the up validator `p` between steps: `p` joins `crashed`. -/
  | crash (p : Node)
  /-- The environment crashes `p` during the reaction of the node action `a`, after `k` of
      its effects: the reaction runs, its first `k` effects are applied, the framework's
      final disk write is skipped, its new memory state is discarded, and `p` joins
      `crashed`. -/
  | crashDuring (p : Node) (a : NodeAction Node Msg Ev) (k : Nat)
  /-- The environment restarts the honest validator `p`, crashed or with an unknown local state,
      whose clock exists, its memory surviving when `keep` is `true`: `p` leaves `crashed`. When
      `p`'s local state is unknown and its clock reads `t`, `p` comes online: its local state becomes
      `Pr.initialLocal p t`, whatever `keep`. When it is known and `p`'s clock reads `t`, its node state becomes its protocol's
      `restart t false` of its disk when `keep` is `false`, and `restart t true` of its memory when
      `keep` is `true`; its disk is kept. Its clock and its view are unchanged. No reaction
      runs. -/
  | restart (p : Node) (keep : Bool)
  /-- A protocol-specific event fires at `p`. -/
  | custom (p : Node) (ev : Ev)
  /-- An adversarial validator signs an arbitrary message and addresses it to `to`. -/
  | adversarial (p : Node) (m : Msg) (recipients : Recipients Node)

/-- Give `p` the local state `r` (`some l` for a known one, `none` for an unknown one), leaving
    every other validator's alone.

    The **only** place the `fun q => if p = q then … else c[q]` pattern is written for the local
    states: the setters that follow are each one call to this with the field they change, so a new
    setter cannot get the map update subtly wrong. Takes the new local state rather than a
    function of the old one — a function-shaped update only yields lemmas mentioning an opaque
    `f c[p]`, whereas with a value `(c.setNode p r)[q]` is `if p = q then r else c[q]` by
    definition. -/
def Config.setNode {Node Msg NodeState : Type} [DecidableEq Node] (p : Node)
    (r : Option (Local Node Msg NodeState)) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  { c with nodes := fun q => if p = q then r else c[q] }

/-! The writes that follow each name what they change, and each is a single `setNode`, a single
update of `sent`, a single update of `clock`, or a sequence of them. An earlier version had
`applyNodeStepResult` go through a `Config.setNodeState`, which cost an extra hop in every proof
about it and made it the odd one out.

Each write to a part of `p`'s local state (a disk write, the memory and the final write of a
completed reaction) changes that part when the local state is known, and changes nothing when it
is unknown (`Option.map`). The steps that run a reaction of `p`, the only callers of these writes,
are enabled only when `p`'s local state is known (`nodeSpec`), so the unknown case is never reached
by a step. The view is not part of the local state, and its one write, `receive`, changes it
whatever the local state. -/

/-- File a delivered message into `p`'s view (`Config.view`), without reacting to it. The view
    exists whatever `p`'s local state, so the message is filed whether `p`'s local state is known
    or unknown, and whether `p` is honest or corrupted. -/
def receive {Node Msg NodeState : Type} [DecidableEq Node] [DecidableEq Msg] (p : Node)
    (m : SignedMsg Node Msg) (c : Config Node Msg NodeState) : Config Node Msg NodeState :=
  { c with view := fun q => if p = q then insert m (c.view p) else c.view q }

/-- Apply one effect of `p`'s reaction: a send puts the addressed message on the wire, signed
    by `p` and keeping the recipients the reaction gave it; a write sets `p`'s disk (and changes
    nothing when `p`'s local state is unknown). -/
def applyEffect {Node Msg NodeState : Type} [DecidableEq Node] (p : Node)
    (ef : NodeEffect Node Msg NodeState) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  match ef with
  | .send a => { c with sent := a.sign p ::ₘ c.sent }
  | .write d => c.setNode p (c[p].map fun l => { l with disk := d })

/-- Apply the effects `effs` of `p`'s reaction, first to last. -/
def applyEffects {Node Msg NodeState : Type} [DecidableEq Node] (p : Node)
    (effs : List (NodeEffect Node Msg NodeState)) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  effs.foldl (fun acc ef => applyEffect p ef acc) c

/-- Apply a completed reaction: its effects in order, then `p`'s new memory state, then the
    framework's write of `Pr.persist` of that state to `p`'s disk. So after the step the
    disk holds the persistent part of the state the step left, whatever the reaction wrote.
    When `p`'s local state is unknown, only the sends are applied.

    Sends are *not* filtered here. A protocol whose validator must stay silent for a while
    (after a restart, say) achieves that by listing no `send` in its own `step`. -/
def applyNodeStepResult {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (res : NodeStepResult Node NodeState Msg)
    (c : Config Node Msg NodeState) : Config Node Msg NodeState :=
  let c₁ := applyEffects p res.effects c
  c₁.setNode p (c₁[p].map fun l => { l with st := res.state, disk := Pr.persist res.state })

/-- Apply a reaction interrupted by a crash after `k` of its effects: its first `k` effects in
    order (all of them when `k` is at or past the list's length), no final write, the new
    memory state discarded, and `p` put into `crashed`. -/
def applyCrashDuring {Node Msg NodeState : Type} [DecidableEq Node] (p : Node)
    (res : NodeStepResult Node NodeState Msg) (k : Nat) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  let c₁ := applyEffects p (res.effects.take k) c
  { c₁ with crashed := insert p c₁.crashed }

/-- `p`'s clock now reads `t`, and exists if it did not: the effect of the step
    `Action.setClock`. One of the two writes of `Config.clock`; the other is the step `corrupt p`,
    which sets `p`'s clock to `none` (`spec`). Which readings a run sets, and at which real times,
    are conditions on executions (`RealStsMulticastMultisetLog.Spec.Conditions`). -/
def setClock {Node Msg NodeState : Type} [DecidableEq Node] (p : Node) (t : Time)
    (c : Config Node Msg NodeState) : Config Node Msg NodeState :=
  { c with clock := fun q => if p = q then some t else c.clock q }

/-- `NodeStep Pr p e pre c'` — `c'` is the configuration `p` reaches by reacting to `e` in
    `pre`, the reaction completed: `p`'s local state `l` and its clock reading `t` in `pre` are
    known, and some reaction the protocol permits at the reading `t` and the memory state `l.st`
    is applied by `applyNodeStepResult`. When `p`'s local state is unknown or its clock does not
    exist, `p` has no reaction, and no `c'` is reached.

    An existential: the reaction is not a function of `(pre, c')`, since the framework's
    final write overwrites the reaction's own disk writes and the configurations do not
    record the order of the effects. -/
def NodeStep {Node Msg NodeState Ev : Type} [DecidableEq Node] (Pr : Protocol Node Msg NodeState Ev)
    (p : Node) (e : Event Node Msg Ev) (pre c' : Config Node Msg NodeState) : Prop :=
  ∃ (l : Local Node Msg NodeState) (t : Time) (res : NodeStepResult Node NodeState Msg),
    pre[p] = some l ∧ pre.clock p = some t ∧ Pr.step p t l.st e res ∧
    c' = applyNodeStepResult Pr p res pre

/-- `CrashDuringStep Pr p e k pre c'` — `c'` is the configuration `p` is left in when a crash
    interrupts its reaction to `e` in `pre` after `k` of the reaction's effects: `p`'s local
    state `l` and its clock reading `t` in `pre` are known, and some reaction the protocol
    permits at the reading `t` and the memory state `l.st` is applied by `applyCrashDuring`.
    When `p`'s local state is unknown or its clock does not exist, no `c'` is reached. -/
def CrashDuringStep {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev) (k : Nat)
    (pre c' : Config Node Msg NodeState) : Prop :=
  ∃ (l : Local Node Msg NodeState) (t : Time) (res : NodeStepResult Node NodeState Msg),
    pre[p] = some l ∧ pre.clock p = some t ∧ Pr.step p t l.st e res ∧
    c' = applyCrashDuring p res k pre

/-- Reacting is always possible at a validator whose local state and clock reading are known,
    from `Protocol.total`. The node actions discharge their `feasible` with this. -/
theorem nodeStep_total {Node Msg NodeState Ev : Type} [DecidableEq Node]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Event Node Msg Ev)
    (pre : Config Node Msg NodeState) (l : Local Node Msg NodeState) (t : Time)
    (hl : pre[p] = some l) (ht : pre.clock p = some t) : ∃ c', NodeStep Pr p e pre c' := by
  obtain ⟨res, he⟩ := Pr.total p t l.st e
  exact ⟨_, l, t, res, hl, ht, he, rfl⟩

/-- What one action does: when it may occur, and how it may change the
    configuration.

    The two halves sit **together, per action**, so they cannot be mismatched: there
    is no way to write an enabling condition belonging to one action beside the
    effect of another, and no way to add an action and forget one half.

    `Effect` is a *relation*, not a function, so a nondeterministic action is
    expressible — the successor need not be determined by the configuration. The
    environment's and the adversary's actions are deterministic, because every choice is
    carried in the action itself (`setClock p t` the reading, `restart p keep` whether the
    memory survived, `crashDuring p a k` the reaction interrupted and how many of its effects are
    applied); an action that runs a reaction has as many successors as the protocol permits
    reactions.

    `feasible` is the price of making enabling conditions syntactic: it says the
    condition does not promise more than the effect can deliver. Event-B calls this
    the *feasibility* proof obligation (FIS) and generates it for exactly this
    reason; TLA+ avoids it by defining `ENABLED A` as "some successor satisfies `A`",
    at the cost of enabledness never being explicit. Discharging it at the definition
    site is what keeps `Execution.Enabled` honest — the alternative, an enabling
    predicate passed alongside an action, has nothing tying the two together. -/
structure ActionSpec (Node Msg NodeState : Type) where
  /-- When the action may occur. -/
  Enabled : Config Node Msg NodeState → Prop
  /-- How it may change the configuration. -/
  Effect : Config Node Msg NodeState → Config Node Msg NodeState → Prop
  /-- Being enabled really does permit a step (Event-B's FIS). -/
  feasible : ∀ c, Enabled c → ∃ c', Effect c c'

/-- The event the node action `na` hands to the protocol: `tick` for a tick, the delivered
    envelope's signed message for a delivery, the protocol's own event for a `custom`. -/
def NodeAction.event {Node Msg Ev : Type} (na : NodeAction Node Msg Ev) : Event Node Msg Ev :=
  match na with
  | .tick => .tick
  | .deliver e => .recv e.toSignedMsg
  | .custom ev => .custom ev

/-- The configuration the reaction of the node action `na` at `p` starts from: for a delivery of
    `e`, `e`'s signed message filed into `p`'s view (`Config.view`), for the environment's
    account of what was delivered (the reaction receives the message through the event `recv`,
    not through the view); for a tick or a `custom` event, `c` itself. No node action changes the
    clock. -/
def NodeAction.prepare {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (p : Node) (na : NodeAction Node Msg Ev) (c : Config Node Msg NodeState) :
    Config Node Msg NodeState :=
  match na with
  | .tick => c
  | .deliver e => receive p e.toSignedMsg c
  | .custom _ => c

/-- The enabling condition and the effect of the node action `na` at `p`, completed: when it
    may occur, and the reaction of `p` to `na`'s event, run from `na.prepare p c` and applied
    in full (`NodeStep`). Each condition requires `p` up and honest, `p ∉ c.crashed` and
    `p ∉ c.adv`, and `p`'s local state `l` and its clock reading `t` known, `c[p] = some l` and
    `c.clock p = some t`: so the only reactions that run are an honest node's, and none runs at
    a validator whose local state is unknown (it has never come online, or it is corrupted). A
    validator whose local state is known always has a clock, since a restart needs one; the
    condition on the clock names the reading `t` the reaction runs at.

    * A tick: no further condition. The tick reaction runs at `p`'s current clock reading. The
      step relation allows any number of ticks at one reading; which ticks a run must contain,
      and by when, is a condition on executions (`TicksWithinR`, `RealStsMulticastMultisetLog.Spec.Conditions`).
    * A delivery of `e`: `e` is on the wire and names `p` among its recipients. Any sent
      envelope may be delivered to any of its recipients that is up and honest, at any real
      time; here, delivery to a crashed honest validator, or to one whose local state is
      unknown, is not enabled, and the envelope stays in `sent`. A delivery to a corrupted
      validator is not a node action: `deliverSpec` adds it, with no reaction.
      When the network must deliver, and to whom it must not, are conditions on executions. The
      reaction runs at `p`'s current clock reading.
    * A protocol-specific event `ev`: the protocol allows it at `p`'s own clock reading `t` and
      memory state `l.st`.

    `spec` uses this for the steps `tick` and `custom`, `deliverSpec` uses it for a delivery to an
    honest validator, and `spec` uses its enabling condition for `crashDuring`, so that a crash
    may interrupt a reaction exactly when the reaction may run.

    Read aloud: an up, honest node whose local state and clock reading are known may take its
    timer interrupt, be delivered a sent envelope addressed to it, or fire an event its protocol
    allows; it then reacts at its current clock reading as its protocol permits, and the reaction
    is applied in full. -/
def nodeSpec {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (na : NodeAction Node Msg Ev) :
    ActionSpec Node Msg NodeState where
  Enabled c :=
    p ∉ c.adv ∧ p ∉ c.crashed ∧
      ∃ (l : Local Node Msg NodeState) (t : Time), c[p] = some l ∧ c.clock p = some t ∧
        match na with
        | .tick => True
        | .deliver e => e ∈ c.sent ∧ e.recipients.Has p
        | .custom ev => Pr.enabled t l.st ev
  Effect c c' := NodeStep Pr p na.event (na.prepare p c) c'
  feasible c h := by
    obtain ⟨-, -, l, t, hl, ht, -⟩ := h
    obtain ⟨l', hl'⟩ : ∃ l', (na.prepare p c)[p] = some l' := by
      cases na <;> exact ⟨l, hl⟩
    exact nodeStep_total Pr p na.event _ l' t hl' (by cases na <;> exact ht)

/-- The enabling condition and the effect of the step `deliver p e`, the delivery of the envelope
    `e` to `p`. It has two cases, by whether `p` is corrupted.

    * `p` is honest, `p ∉ c.adv`: the node action of a delivery (`nodeSpec Pr p (.deliver e)`).
      It is enabled when `p` is up (outside `crashed`, with its local state and its clock reading
      known), `e` is on the wire and `e` names `p` among its recipients; `e`'s signed message is
      filed into `p`'s view and `p`'s reaction to it runs at `p`'s clock reading, applied in full.
    * `p` is corrupted, `p ∈ c.adv`: enabled when `e` is on the wire and names `p` among its
      recipients, whether `p` is crashed or not; `e`'s signed message is filed into `p`'s view
      (`receive`), and nothing else changes. No protocol code runs: a corrupted validator has no
      local state and no clock.

    A delivery to a crashed honest validator, or to an honest validator whose local state is
    unknown (it has never come online), is not enabled. Each case's effect carries its own
    condition on `p ∈ c.adv`, so the two cases never mix.

    Read aloud: a sent envelope addressed to `p` may be delivered to `p` when `p` is corrupted, and
    is then only filed into `p`'s view; or when `p` is up and honest, and `p` then reacts to it as
    its protocol permits. -/
def deliverSpec {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (p : Node) (e : Envelope Node Msg) :
    ActionSpec Node Msg NodeState where
  Enabled c :=
    (p ∈ c.adv ∧ e ∈ c.sent ∧ e.recipients.Has p) ∨ (nodeSpec Pr p (.deliver e)).Enabled c
  Effect c c' :=
    (p ∈ c.adv ∧ c' = receive p e.toSignedMsg c) ∨
      (p ∉ c.adv ∧ (nodeSpec Pr p (.deliver e)).Effect c c')
  feasible c h := by
    by_cases hp : p ∈ c.adv
    · exact ⟨_, Or.inl ⟨hp, rfl⟩⟩
    · obtain ⟨c', hc'⟩ :=
        (nodeSpec Pr p (.deliver e)).feasible c (h.resolve_left fun h' => hp h'.1)
      exact ⟨c', Or.inr ⟨hp, hc'⟩⟩

/-- Each action's enabling condition and effect.

    Every step that runs a reaction requires its node up and honest, `p ∉ c.crashed` and
    `p ∉ c.adv`, with its local state and its clock reading known: so the only reactions that
    run are an honest node's, completed (`tick`, `deliver`, `custom`) or interrupted
    (`crashDuring`). At a validator in `c.adv` no reaction runs: `adversarial` is enabled there,
    and only it puts on the wire what no reaction sent; `deliver` is enabled there too, and only
    files the delivered message into the validator's view (`deliverSpec`). `restart` and
    `setClock` run no reaction; `setClock` is enabled at a node not corrupted, up or crashed,
    before or after it has come online, and `restart` only once the node's clock exists.
    `corrupt` empties the node's local state and its clock, and keeps its view. Every condition
    reads the configuration and nothing else: no time, which is the execution's
    (`Execution.stamp`).

    A delivery reads the recipients: `deliver p e` is enabled only when `e.recipients.Has p`.
    The recipients reach no view: `p` is delivered `e.toSignedMsg`, as before.

    Read aloud: for each action, when it may be taken and what configuration it may lead to,
    both read off the configuration alone. -/
def spec {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) : Action Node Msg Ev → ActionSpec Node Msg NodeState
  -- The environment sets the clock of a validator `p` that is not corrupted to the reading `t`.
  -- No protocol code runs. Once the clock exists, `t` is greater than its current reading, and
  -- the step is enabled whether `p` is up or crashed: the clock is the node's hardware, and it
  -- advances while the node is crashed. Before the clock exists, the step starts it at any
  -- reading `t`: `p`'s local state may be unknown (it has not come online yet) or known. A
  -- `restart` needs the clock, so a validator's clock starts before it first comes online. Not
  -- enabled at a corrupted validator, whose clock `corrupt` emptied: no clock is kept for it.
  | .setClock p t => {
      Enabled c :=
        p ∉ c.adv ∧
          match c.clock p with
          | some r => r < t
          | none => True
      Effect c c' := c' = setClock p t c
      feasible _ _ := ⟨_, rfl⟩ }
  -- The timer interrupt: `p` reacts at its current clock reading (`nodeSpec`).
  | .tick p => nodeSpec Pr p .tick
  -- The envelope `e` is delivered to `p`: at an honest `p`, which reacts to its signed message
  -- (`nodeSpec`); at a corrupted `p`, filed into its view only (`deliverSpec`).
  | .deliver p e => deliverSpec Pr p e
  -- The environment corrupts a validator not yet corrupted: it joins `adv` for good, its local
  -- state becomes unknown, `none`, and its clock is emptied, `none`. Neither is set again, since
  -- `restart` and `setClock` are not enabled at a corrupted validator. From then on it never
  -- ticks and fires no protocol event; what it sends of its own goes through `adversarial`. Its
  -- view is kept, and deliveries go on filing messages into it (`deliverSpec`).
  | .corrupt p => {
      Enabled c := p ∉ c.adv
      Effect c c' := c' =
        { c.setNode p none with
            adv := insert p c.adv
            clock := fun q => if p = q then none else c.clock q }
      feasible _ _ := ⟨_, rfl⟩ }
  -- The environment crashes a validator outside `crashed` between steps: it joins `crashed`, so
  -- it does nothing and receives nothing from here on. Its local state is untouched, so its disk
  -- is `Pr.persist` of the state its last completed step left. A corrupted validator, or one that
  -- has never come online, may crash, to no effect on what the adversary can do; the second
  -- comes online at its restart as it would without the crash.
  | .crash p => {
      Enabled c := p ∉ c.crashed
      Effect c c' := c' = { c with crashed := insert p c.crashed }
      feasible _ _ := ⟨_, rfl⟩ }
  -- The environment crashes `p` during the reaction of the node action `a`, after `k` of
  -- its effects. Enabled when `a`'s own step is. The reaction `a` would run runs, from the
  -- configuration `a`'s own step starts it from; its first `k` effects are applied (sends
  -- on the wire, writes to the disk), all of them when `k` is at or past the list's length;
  -- the framework's final write is skipped; the new memory state is discarded; `p` joins
  -- `crashed`.
  | .crashDuring p a k => {
      Enabled := (nodeSpec Pr p a).Enabled
      Effect c c' := CrashDuringStep Pr p a.event k (a.prepare p c) c'
      feasible c h := by
        obtain ⟨-, -, l, t, hl, ht, -⟩ := h
        obtain ⟨l', hl'⟩ : ∃ l', (a.prepare p c)[p] = some l' := by
          cases a <;> exact ⟨l, hl⟩
        obtain ⟨res, he⟩ := Pr.total p t l'.st a.event
        exact ⟨_, l', t, res, hl', by cases a <;> exact ht, he, rfl⟩ }
  -- The environment restarts an honest validator that is crashed, or whose local state is
  -- unknown, and whose clock exists, its memory surviving when `keep` is `true`. It leaves
  -- `crashed`. A pure change of state: no reaction runs and nothing is sent; its clock, which
  -- reads some `t`, is unchanged.
  --
  -- * Its local state is known as `l`: its node state is its protocol's `restart` at the reading
  --   `t`, of its disk `l.disk` when `keep` is `false` and of its memory `l.st` when `keep` is
  --   `true`. Its disk is kept.
  -- * Its local state is unknown (it has never come online; a corrupted validator is not
  --   restarted): it comes online, its local state `Pr.initialLocal p t`, whatever `keep`.
  --
  -- Its view (`Config.view`) is not touched in either case: the view is every message delivered
  -- to the validator, which the environment reads, not the validator's memory (what the validator
  -- kept of a delivered message is in its node state, and `restart` says what survives).
  --
  -- A validator whose clock does not exist is not restarted: it has never come online, and it
  -- comes online only once a `setClock` has started its clock. So a validator whose local state is
  -- known always has a clock, and `Protocol.restart` is always handed a reading.
  | .restart p keep => {
      Enabled c := p ∉ c.adv ∧ (p ∈ c.crashed ∨ c[p] = none) ∧ c.clock p ≠ none
      Effect c c' := ∃ t : Time, c.clock p = some t ∧ c' =
        { c.setNode p (some (match c[p] with
            | some l => { l with st := Pr.restart t keep (if keep then l.st else l.disk) }
            | none => Pr.initialLocal p t))
          with crashed := c.crashed.erase p }
      feasible c h := by
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp h.2.2
        exact ⟨_, t, ht, rfl⟩ }
  -- A protocol-specific event, if the protocol allows it at the validator's own
  -- clock reading (`nodeSpec`).
  | .custom p ev => nodeSpec Pr p (.custom ev)
  -- An adversarial validator signs anything, addressed to anyone.
  | .adversarial p m recipients => {
      Enabled c := p ∈ c.adv
      Effect c c' := c' =
        { c with sent := { sender := p, msg := m, recipients := recipients } ::ₘ c.sent }
      feasible _ _ := ⟨_, rfl⟩ }

/-- The step relation: enabled, and then the effect. *When* messages must be
    delivered, and how clocks relate to the real time, are properties of the model,
    imposed on executions rather than here.

    Read aloud: `a` may be taken from `c`, and `c'` is a configuration `a` may lead to from
    `c`. -/
def Step {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (a : Action Node Msg Ev)
    (c c' : Config Node Msg NodeState) : Prop :=
  (spec Pr a).Enabled c ∧ (spec Pr a).Effect c c'

/-- Initial configurations: every validator's local state unknown and its clock absent, since
    no validator has come online yet, every validator's view empty, and nothing sent. Each
    validator's clock is started by a `setClock`, and the validator comes online by a later `restart`, which gives it
    `Pr.initialLocal p t` at its clock reading `t` and is enabled only once the clock exists.
    `adv` and `crashed` are not constrained: the environment starts from any corrupted set and
    any crashed set, as the framework's schedule could say anything at time `0`. A validator
    corrupted from the start never has a clock, since `setClock` is not enabled at it. A model that
    wants every corruption recorded as a `corrupt` step assumes `(x[0]).adv = ∅` of its
    executions; likewise `(x[0]).crashed = ∅`. The run's start at the real time `0` is the
    execution's (`Execution.init_stamp`).

    No protocol is a parameter: the protocol enters at the first `restart` of each validator.

    Read aloud: every validator's local state is unknown, no validator's clock exists, every
    validator's view is empty, and nothing has been sent. -/
def Init {Node Msg NodeState : Type} (c : Config Node Msg NodeState) : Prop :=
  (∀ p : Node, c[p] = none) ∧ (∀ p : Node, c.clock p = none) ∧ (∀ p : Node, c.view p = ∅) ∧
    c.sent = 0

/-- A labelled transition system: initial states, and a labelled step relation
    that may be nondeterministic and partial.

    The framework's own, so that `Framework/` depends on nothing outside itself.
    Only the structure is here — no reachability or inductive-invariant machinery,
    since the framework carries no proofs while its shape is being iterated on.
    `Common/System.lean` has that machinery for the `Sts` attempt; when proofs
    return, **build it here rather than importing `Common`**, because liveness needs
    statements over `Execution` that a state-based invariant cannot express. -/
structure System (SystemState : Type u) (Label : Type v) where
  /-- The states the system may start in. -/
  Init : SystemState → Prop
  /-- Labelled transition relation. -/
  Step : Label → SystemState → SystemState → Prop

/-- The protocol as a transition system. -/
def system (Node Msg NodeState Ev : Type) [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) :
    System (Config Node Msg NodeState) (Action Node Msg Ev) where
  Init := Init
  Step := Step Pr

end Framework.RealStsMulticastMultisetLog

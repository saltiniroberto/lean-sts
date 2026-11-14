module
public import RealStsMulticastMultisetLog.Spec.Execution
public import RealStsMulticastMultisetLog.Spec.Observable

@[expose] public section

/-!
# Conditions on executions

The bare framework (its states, its steps and its executions:
`RealStsMulticastMultisetLog.Spec.Protocol` and `RealStsMulticastMultisetLog.Spec.Execution`)
assumes none of the definitions on this page. Each is a condition on executions, which no step of
the framework reads and which a statement takes as a hypothesis, or a reading of an execution that
such a condition uses. Each predicate here is à la carte: a model is whichever conjunction of them
a paper assumes.

* The environment: `NoCrashDuring`.
* Clocks and real time: `ClockWithinSkew`, with its instances `ClockNotAhead` and `ClockAtTime`.
* Fairness: `WeakFair`, `StrongFair`, `ClockAdvancesWithin`, `TicksWithin` (with
  `DiligentWithin`, their conjunction) and `ActsWithinSkew`.
* The network: `DeliveredBeforeActing`, `CatchUpAfterRestart` and `SyncedWithinBy`, with `DueBy`,
  the deadline functions `syncDeadline` and `deadlineOutside`, the readings `ActingStep`
  and `TickStep` (one of which the three take as their acting steps), and the readings
  `UpBetween`, `UpAndHonestThroughout` and `UpAndHonestUntilActing`.
* Ticks and the adversary's sends: `TickOncePerReading` and `UnforgeableSends`.

No condition here is about a particular kind of protocol. A condition that reads what only some
protocols have (a validator set, committees, blocks) belongs to the project that states it.

## Each definition is written once, on observed runs

Each definition here that reads an execution, except `WeakFair` and `StrongFair` (which read
`Execution.Enabled`, the step relation's enabling condition), is written once, on observed runs
(`ObservedRun` of `ObservedConfig`, `RealStsMulticastMultisetLog.Spec.Execution`: the actions, the
stamps, and in each configuration the clocks, the nodes' values, the views, the sent envelopes, the
corrupted set and the crashed set). A run is an observed run (`Execution` extends `ObservedRun`), its
configurations holding each node's local state, so a condition on a run `π` is the condition on `π`
itself (through its projection `π.toObservedRun`), and a condition on what is read of `π` is the
condition on `observe readLocal π`. The readings `x[i].clock p`, `x[i][p]`, `x[i].view p`,
`x[i].sent`, `x[i].adv`, `x[i].crashed`, `x.lbl j` and `x.stamp i` read an observed run as they read
a run.

What a condition reads of the protocol is a parameter of it: a reading of a node's value
(`serves`), who a message's object is attributed to and which objects a message includes (`author`,
`carries`). On a run a node's value is its local state `l`; a parameter that reads the protocol's
memory state reads `l.st`.

## Crashes, cut networks, corrupted validators

Whether a crash may interrupt a reaction is one of these conditions too. The step relation has both
kinds of crash: `crash p`, between steps, after the framework's write of `Pr.persist` of the last
state to the disk; and `crashDuring p a k`, after the first `k` effects of the reaction of `a`, with
the final write skipped. `NoCrashDuring` excludes the second kind: under it every reaction
completes, as in a model whose reactions are atomic.

No condition here says that a node's network is cut. A model that needs a cut network states a
condition of its own.

A delivery `deliver p e` to a corrupted validator `p` is a step of the bare framework
(`deliverSpec`): it files the message into `p`'s view and runs no protocol code. The network's
conditions never meet it, since a corrupted validator takes no acting step and is not up.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

open ObservedRun

/-! ### The environment

Corruption is permanent by construction (`corrupt` only inserts into `adv`), so no condition
says it. No condition says who is up when: a model that needs a node to participate throughout a
real-time window states a condition of its own on the configurations in force during the window
(`InForce`), for example that the node is outside `crashed` and its local state is known
in each. -/

/-- No crash ever interrupts a reaction: no step of `x` is a `crashDuring`.

    Under it every crash is a `crash p`, taken between steps, when `p`'s disk is `Pr.persist`
    of the state its last completed step left (the framework writes it at the end of every
    completed reaction). So a restart losing memory, `restart p false`, sees exactly the
    persistent part of the state the last step left, and reactions are atomic.

    Read aloud: no step of `x` is labelled `crashDuring`. -/
def NoCrashDuring {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (k : Nat) (p : Node) (a : NodeAction Node Msg Ev) (j : Nat), lbl x k ≠ .crashDuring p a j

/-! ### Clocks and real time

The step relation does not read the real time. No node's clock exists at the start; the first
`setClock p t` starts it, at any reading, whether the node is up or crashed, and the node's first
restart, which brings it online, comes after it. From then on it moves only by `setClock p t`, each
time to a strictly greater reading, whether the node is up or crashed, until the node is corrupted:
`corrupt p` empties the clock, and `setClock p t` is not enabled at a corrupted node. No other step
changes it, a restart included. So while a node is not corrupted its clock strictly increases along
a run. What the step relation says **nothing** about is how a reading relates to the real time at
which it is set: `setClock p t` may set `p`'s clock to any reading greater than its current one, or
start it at any reading, at any real time. That relation is a condition on executions,
`ClockWithinSkew ΔClockAhead ΔClockBehind`, with two real bounds for all nodes: `ΔClockAhead`, how
far a clock may run ahead of the real time, and `ΔClockBehind`, how far it may lag. A property is
then in one of these classes, weakest first:

* **Timeless**: mentions neither the stamps nor the clocks, so it holds however the clocks
  behave. Accountable safety belongs here.
* **Clocks within a skew**: assumes `ClockWithinSkew ΔClockAhead ΔClockBehind`. Its instances are
  `ClockNotAhead ΔClockBehind` (`ΔClockAhead = 0`: no clock runs ahead) and `ClockAtTime`
  (`ΔClockAhead = ΔClockBehind = 0`: one shared clock); they are abbreviations, not definitions of
  their own. Liveness needs this, plus `ClockAdvancesWithin ΔClockAhead ΔClockBehind` and
  `TicksWithin ΔClockBehind` (their conjunction is `DiligentWithin`). That the real
  time does not stop is the field `ObservedRun.progress`, not a condition. -/

/-- Every change of a clock is within the bounds of the real time it is taken at: a step
    `setClock p t` is taken at a real time in `[t − ΔClockAhead, t + ΔClockBehind]`. `ΔClockAhead`
    is how far a node's clock may run ahead of the real time (its change to `t` as early as
    `t − ΔClockAhead`), and `ΔClockBehind` how far it may lag (as late as `t + ΔClockBehind`); one
    pair for all nodes. Both are meant to be at least `0`; a statement that takes the condition
    assumes that.

    The real time of the change is the stamp of the configuration the step enters,
    `x.stamp (i + 1)`, and it is each node's own: the clocks are digital, the steps that set them
    are not. Every `setClock` is bound, whether the node is up or crashed: the clock runs while the
    node is crashed. A corrupted node has no clock and takes no `setClock` (the bare framework's
    `corrupt` empties it, and its `setClock` is not enabled at a corrupted node), so nothing here
    reads a corrupted node's clock. Only `setClock` gives a clock a reading, and a clock does not
    exist before its first `setClock`, so a step of `p` at a reading `t` comes after `p`'s clock was
    set to `t`, at a real time no earlier than `t − ΔClockAhead`.

    Read aloud: every node's clock comes to read each reading `t` at a real time no earlier than
    `t − ΔClockAhead` and no later than `t + ΔClockBehind`. -/
def ClockWithinSkew {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockAhead ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (i : Nat) (p : Node) (t : Time), lbl x i = .setClock p t →
    (t : ℝ) - ΔClockAhead ≤ stamp x (i + 1) ∧ stamp x (i + 1) ≤ t + ΔClockBehind

/-- No clock runs ahead: `ClockWithinSkew` with `ΔClockAhead = 0`, every change of a clock to `t`
    at a real time in `[t, t + ΔClockBehind]`. An abbreviation of the instance, not a definition of
    its own.

    Read aloud: no node's clock comes to read `t` before the real time reaches `t`, and each comes
    to read it at most `ΔClockBehind` after. -/
abbrev ClockNotAhead {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ClockWithinSkew 0 ΔClockBehind x

/-- One shared clock: `ClockWithinSkew` with `ΔClockAhead = ΔClockBehind = 0`, every change of a
    clock to `t` at the real time `t` exactly. An abbreviation of the instance, not a definition of
    its own.

    Read aloud: every node's clock comes to read each reading `t` at the real time `t`. -/
abbrev ClockAtTime {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ClockWithinSkew 0 0 x

/-! ### Fairness

A change of a clock and a tick are transitions of their own, so nothing forces either to happen:
the real time may pass forever while some validator's clock stands still, or while it never takes
its timer interrupt, and no liveness argument survives that. Hence weak fairness, stated in the
textbook shape — *continuously enabled implies eventually taken* — which is what the step labels
are for, and `ClockAdvancesWithin` and `TicksWithin`, which say by when each change of a clock and
each tick is taken.

Enabledness is not a parameter: it comes from the action's own `ActionSpec`, so a
fairness assumption cannot describe the wrong condition. -/

/-- Weak fairness for one action: continuously enabled implies eventually taken.

    Read aloud: if from some step on `a` is enabled at every step, then `a` is taken at one of
    them. -/
def WeakFair {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (a : Action Node Msg Ev) : Prop :=
  ∀ i : Nat, (∀ j, i ≤ j → x.Enabled j a) → ∃ j, i ≤ j ∧ x.lbl j = a

/-- Strong fairness: enabled infinitely often implies eventually taken. Needed for a
    validator that is up only now and then, rather than staying up.

    Read aloud: if `a` is enabled at steps as late as one likes, then `a` is taken after every
    step. -/
def StrongFair {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (x : Exec Pr) (a : Action Node Msg Ev) : Prop :=
  (∀ i : Nat, ∃ j, i ≤ j ∧ x.Enabled j a) → ∀ i : Nat, ∃ j, i ≤ j ∧ x.lbl j = a

/-- A condition on executions, which a statement takes as a hypothesis. While a node is up (not
    crashed, with its local state known) and not corrupted, its clock, once started at any reading,
    comes to every greater reading; a crash or a corruption by the real time `t + ΔClockBehind`
    releases the node from a reading `t`. The real time at which the clock comes to `t` is not
    bounded here: when a statement takes `ClockWithinSkew` too, that condition puts it in the
    window of `t`, the real-time interval `[t − ΔClockAhead, t + ΔClockBehind]`
    (`clockAdvancesWithin_bounded`, `RealStsMulticastMultisetLog.Analysis.Observable`). The formula
    does not read `ΔClockAhead`; the parameter matches `ClockWithinSkew`'s.

    **Real times of steps and of configurations.** `x.stamp i` is the real time at which
    configuration `i` is entered. Step `i` leads from configuration `i` to configuration `i + 1`,
    so its real time is `x.stamp (i + 1)`, the stamp of the configuration it enters; `x.stamp i` is
    the real time of the step before it.

    **The formula, clause by clause.**

    1. The premise.

           ∀ (t : Time) (p : Node) (i : Nat) (t' : Time),
             p ∉ x[i].crashed → x[i][p] ≠ none → p ∉ x[i].adv → x[i].clock p = some t' →
               t' < t → …

       Read aloud: for every node `p`, every reading `t`, and every configuration `i` in which `p`
       is not crashed, has its local state known (it has come online), is not corrupted, and its
       clock exists and reads some `t'` less than `t`.

       So a reading `t` is asked of `p` only through a configuration where `p` is up and not
       corrupted and its clock has shown a reading less than `t`. A clock that never starts is
       asked nothing. A clock started at `t₀` (the first `setClock p t₀`, at any reading) is never
       asked `t₀` or a reading less than it, since a clock only moves forward while it exists and
       once emptied by a corruption never exists again. While `p` is crashed no configuration binds
       it, so its clock may stand still, skip readings, or come to a reading outside that reading's
       window; only `ClockWithinSkew`, another condition on executions, bounds the real time of a
       `setClock` taken then. A corrupted node has no clock (the bare framework's `corrupt` empties
       it, and its `setClock` is not enabled at a corrupted node), so `p ∉ x[i].adv` follows from
       `x[i].clock p = some t'` (and from `x[i][p] ≠ none`); it is written out so that the premise
       reads "up and not corrupted".

    2. The conclusion is a disjunction of two cases.

           (∃ j : Nat, …) ∨ (∃ j : Nat, …)

       Read aloud: one of the two cases of clauses 3 and 4 happens.

    3. The clock comes to `t`.

           ∃ j : Nat, x.lbl j = .setClock p t

       Read aloud: some step `j` sets `p`'s clock to `t`.

       That step comes after configuration `i`: `p`'s clock reads less than `t` there and only
       moves forward. The case asks only that the step happen. Its real time `x.stamp (j + 1)` is
       bounded by `ClockWithinSkew`, when a statement takes both: at least `t − ΔClockAhead` and
       at most `t + ΔClockBehind`.

    4. The release: a crash or a corruption after configuration `i`, by the end of `t`'s window.

           ∃ j : Nat, i < j ∧ x.stamp j ≤ t + ΔClockBehind ∧ (p ∈ x[j].crashed ∨ p ∈ x[j].adv)

       Read aloud: some configuration `j` after `i`, entered by the real time `t + ΔClockBehind`,
       has `p` crashed or corrupted.

       Here `x.stamp j` is the real time configuration `j` is entered, that is, the real time of
       the step `j − 1` that crashed or corrupted `p` (or of a later step). Only `crash p`, a
       `crashDuring p a n` and `corrupt p` put `p` in `crashed` or in `adv`. A crash before
       configuration `i` releases nothing: once `p` is restarted with its clock still reading less
       than `t`, the configuration the restart enters binds `p` for `t` again.

    **Consequences**, for a statement that takes `ClockWithinSkew` too, which bounds the real time
    of every `setClock`. A node is restarted only with its clock within the bounds of the real time.
    In a configuration `i` where `p` is up and not corrupted and its clock reads `t'`, the
    reading `t' + 1` is owed, and both cases come after configuration `i`; so configuration `i` was
    entered, and is left, by the real time `t' + 1 + ΔClockBehind` (read off the step relation, not
    proved). A restart of a node whose clock fell behind while it was crashed is therefore preceded
    by a `setClock` that brings the clock forward (enabled while the node is crashed, and free to
    skip readings), or the run does not satisfy the condition.

    A node that has not yet come online (its local state unknown, `x[i][p] = none`, and not
    corrupted) is asked nothing until its local state is known: no configuration binds it, so its
    clock, once started, may stand still or skip readings, as a crashed node's may. Such a node
    takes no step of its own (a tick, a protocol event and a delivery's reaction each need the local
    state), so nothing it does depends on its clock until it comes online, and from the
    configuration in which it comes online the condition binds it as it binds every node that is up.

    This is what keeps the clock of a node that is up moving, and it is a fairness property rather
    than a consequence of how clocks work: nothing in the step relation forces a `setClock` to be
    taken. The ticks are a separate condition on executions, `TicksWithin`.

    A consequence at a restart, again with `ClockWithinSkew`: the condition binds `p` in the
    configuration a `restart p keep` enters, whatever its real time, since that configuration has
    `p` outside `crashed`, not corrupted, and with its local state known (the restart that brings
    `p` online for the first time included). So if `p` restarts at a real time `τ` while its clock
    reads `t'`, every reading `t > t'` whose window has closed (`t + ΔClockBehind < τ`) can be met
    neither by a `setClock p t` (the clock reads less than `t`, so none was taken, and a later one
    is outside the window) nor by a crash by `t + ΔClockBehind`: the execution fails the condition.
    Hence a node comes back up only with its clock within the skew bounds of the real time, up to
    one reading; the environment brings a crashed node's clock forward by `setClock` before the
    restart.

    Read aloud: whenever a node `p` is up (not crashed, with its local state known) and not
    corrupted, and its clock reads less than a reading `t`, either `p`'s clock comes to read `t`, or
    `p` crashes or is corrupted afterwards, by the real time `t + ΔClockBehind`. The clock of a node
    crashed or not yet online is not read, and a clock that never starts is asked nothing. -/
def ClockAdvancesWithin {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockAhead ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (t : Time) (p : Node) (i : Nat) (t' : Time),
    p ∉ crashed x i → state x i p ≠ none → p ∉ adv x i → clock x i p = some t' → t' < t →
      (∃ j : Nat, lbl x j = .setClock p t) ∨
      (∃ j : Nat, i < j ∧ stamp x j ≤ t + ΔClockBehind ∧ (p ∈ crashed x j ∨ p ∈ adv x j))

/-- A condition on executions, which a statement takes as a hypothesis. A node up and honest when
    its clock comes to read `t` takes a tick while its clock reads `t`, by the real time
    `t + ΔClockBehind`, unless it is corrupted or crashes first.

    **Real times of steps and of configurations.** `x.stamp i` is the real time at which
    configuration `i` is entered. Step `i` leads from configuration `i` to configuration `i + 1`,
    so its real time is `x.stamp (i + 1)`, the stamp of the configuration it enters; `x.stamp i` is
    the real time of the step before it.

    **The formula, clause by clause.**

    1. The premise: a step that sets `p`'s clock to `t`.

           ∀ (i : Nat) (p : Node) (t : Time), x.lbl i = .setClock p t → …

       Read aloud: for every step `i` that sets a node `p`'s clock to a reading `t`.

       Every such step counts, the first one included. A clock comes to each reading at most once,
       since it only moves forward while it exists and once emptied never exists again.

    2. The node is up, honest and online at that step.

           p ∉ x[i].crashed → p ∉ x[i].adv → x[i][p] ≠ none → …

       Read aloud: `p` is not crashed, not corrupted, and its local state is known (it has come
       online) in configuration `i`, the one the step `setClock p t` is taken from.

       `setClock` changes neither `crashed`, nor `adv`, nor the local state, so configurations `i`
       and `i + 1` agree on all three. At a clock's first reading the node is not yet online (a
       restart needs the clock), so no tick is asked there.

    3. A later step, while the clock still reads `t`, by the end of `t`'s window.

           ∃ j : Nat, i < j ∧ x[j].clock p = some t ∧ x.stamp (j + 1) ≤ t + ΔClockBehind ∧ …

       Read aloud: some step `j` after `i`, taken from a configuration where `p`'s clock still
       reads `t`, at a real time `x.stamp (j + 1)` at most `t + ΔClockBehind`.

       `x[j].clock p = some t` says that no `setClock p` came between `i` and `j`. The deadline is
       `t + ΔClockBehind` whenever the clock came to `t`: a run in which a node up and honest has
       its clock come to `t` later than `t + ΔClockBehind` does not satisfy the condition
       (`ClockWithinSkew` and `ClockAdvancesWithin` each exclude such a change too).

    4. The four ways the step `j` may be.

           x.lbl j = .tick p ∨ x.lbl j = .corrupt p ∨ x.lbl j = .crash p ∨
             ∃ (a : NodeAction Node Msg Ev) (n : Nat), x.lbl j = .crashDuring p a n

       Read aloud: step `j` is `p`'s timer interrupt, or `p`'s corruption, or a crash of `p`
       between steps, or a crash of `p` during one of its reactions (a tick included).

       The corruption and the two crashes are there because the environment's steps may come at
       any real time; a run in which `p` crashes before its tick, or during it, is a run, and the
       condition does not ask for a tick it cannot take.

    **Consequences.** A node crashed, or not yet online, when its clock comes to read `t`, and
    restarted while its clock reads `t`, is not asked to tick at `t` (it may: `tick p` is enabled
    once it is up). Its restart may come at any real time before its clock's next change, so no
    deadline in the window of `t` fits it.

    This is what makes a node that is up act at each reading, and it is a fairness property rather
    than a consequence of how clocks work: nothing in the step relation forces a `tick` to be
    taken. That the clock moves is a separate condition on executions, `ClockAdvancesWithin`.

    Read aloud: whenever a node `p`'s clock comes to read `t` while `p` is up and honest, `p` takes
    its timer interrupt at the reading `t` by the real time `t + ΔClockBehind`, unless it is
    corrupted or crashes first. -/
def TicksWithin {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (i : Nat) (p : Node) (t : Time), lbl x i = .setClock p t →
    p ∉ crashed x i → p ∉ adv x i → state x i p ≠ none →
      ∃ j : Nat, i < j ∧ clock x j p = some t ∧ stamp x (j + 1) ≤ t + ΔClockBehind ∧
        (lbl x j = .tick p ∨ lbl x j = .corrupt p ∨ lbl x j = .crash p ∨
          ∃ (a : NodeAction Node Msg Ev) (n : Nat), lbl x j = .crashDuring p a n)

/-- A condition on executions, which a statement takes as a hypothesis. A node does not act at a
    stale reading: a tick or a restart taken while its clock reads `t` is at a real time at most
    `t + ΔClockBehind`.

    **Real times of steps and of configurations.** `x.stamp i` is the real time at which
    configuration `i` is entered. Step `i` leads from configuration `i` to configuration `i + 1`,
    so its real time is `x.stamp (i + 1)`.

    **The formula, clause by clause.**

    1. A tick or a restart of `p`.

           ∀ (i : Nat) (p : Node) (t : Time),
             (x.lbl i = .tick p ∨ ∃ keep : Bool, x.lbl i = .restart p keep) → …

       Read aloud: for every step `i` that is `p`'s timer interrupt or a restart of `p`, with or
       without its memory.

    2. Taken while `p`'s clock reads `t`.

           x[i].clock p = some t → …

       Read aloud: in configuration `i`, the one the step is taken from, `p`'s clock reads `t`.

       Neither step changes the clock, so the tick's reaction, and the restart's rebuilt state, are
       at the reading `t`.

    3. By the end of `t`'s window.

           x.stamp (i + 1) ≤ t + ΔClockBehind

       Read aloud: the step's real time is at most `t + ΔClockBehind`.

    **Why the other conditions do not give it.** `ClockWithinSkew` bounds the real time of the step
    that sets a clock to `t`, not of the steps taken while the clock reads `t`.
    `ClockAdvancesWithin` moves the clock past `t` by `t + ΔClockBehind` only while the node is up
    and honest: a node crashed while its clock reads `t` keeps that reading through its crash, and
    without this condition it may restart, and then tick, at the reading `t` at any later real time.
    The lower end of the window needs no condition of its own: a clock reads `t` only after a
    `setClock` to `t`, which `ClockWithinSkew` puts at a real time at least `t − ΔClockAhead`.

    Read aloud: every tick and every restart a node takes while its clock reads `t` is at a real
    time at most `t + ΔClockBehind`. -/
def ActsWithinSkew {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (i : Nat) (p : Node) (t : Time), (lbl x i = .tick p ∨ ∃ keep : Bool, lbl x i = .restart p keep) →
    clock x i p = some t → stamp x (i + 1) ≤ t + ΔClockBehind

/-- A condition on executions, which a statement takes as a hypothesis. It is both
    `ClockAdvancesWithin` and `TicksWithin`: an abbreviation of their conjunction, not a
    definition of its own; a statement that needs only one of the two takes that one.

    **The formula, clause by clause.**

    1. The clock condition.

           ClockAdvancesWithin ΔClockAhead ΔClockBehind x

       Read aloud: while a node is up (not crashed, with its local state known) and not corrupted,
       its clock, once started, comes to each greater reading `t` between the real times
       `t − ΔClockAhead` and `t + ΔClockBehind`, unless the node crashes or is corrupted first, by
       the real time `t + ΔClockBehind`.

    2. The tick condition.

           TicksWithin ΔClockBehind x

       Read aloud: a node up and honest when its clock comes to read `t` takes its timer
       interrupt at `t` by the real time `t + ΔClockBehind`, unless it is corrupted or crashes
       first.

    The real time of a step `i` is `x.stamp (i + 1)`, the stamp of the configuration it enters,
    in both.

    Read aloud: both the clock condition `ClockAdvancesWithin` and the tick condition
    `TicksWithin` hold. -/
abbrev DiligentWithin {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (ΔClockAhead ΔClockBehind : ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ClockAdvancesWithin ΔClockAhead ΔClockBehind x ∧ TicksWithin ΔClockBehind x

/-! ### Network

The network's promise is three conditions on executions, and a statement takes only the ones it
needs:

* `DeliveredBeforeActing acting dl`: an envelope sent to a node that is up from the sending to its
  acting step reaches it after the sending and before that step once its deadline has passed;
* `CatchUpAfterRestart acting dl dlW`: a node that restarted after an envelope was sent to it is
  brought that envelope again after its last restart, once the envelope's deadline from the sending
  and a deadline from each such restart have passed;
* `SyncedWithinBy acting serves sync`: what an honest node that is up serves to a peer that asks
  is already served by, or reaches, every node up and honest until it acts at or after the sync
  deadline, the delivery at a step after which that node stays up and honest until that acting step.

Which steps count as a node's acting steps is a parameter of the three, `acting`, a reading of an
execution: `acting x k p` says that step `k` of `x` is an acting step of `p`. This page gives two
readings: `ActingStep` (a tick, a protocol event, or a crash interrupting one of the two)
and `TickStep` (a tick only). A statement passes the reading it means; the conditions promise a
delivery before each step the reading names, and no other.

Each deadline is a function of the message and of the real time it counts from (a sending, a
restart, a serving), so that one condition covers a network synchronous from a time on
(`syncDeadline`), a network synchronous outside one asynchronous period (`deadlineOutside`), and a
delay per kind of message. The conditions read the stamps, the steps and the configurations only.

"Up" is read on the configuration: outside `crashed`, with the local state known. A validator whose
local state is known is not corrupted (`corrupt` empties the local state, and no step gives a
corrupted validator one back), so a validator up in a configuration is honest there, and one that
has not yet come online is not up.

Every sent envelope is covered by `DeliveredBeforeActing` and `CatchUpAfterRestart`. A model in
which some envelopes are owed nothing (a message gossiped only during a window of its own, say)
adds a filter as a hypothesis of the two. -/

/-- Step `k` of `x` is an acting step of `p`: `p`'s timer interrupt, one of `p`'s protocol events,
    or a crash interrupting one of the two. A reading of an execution that the conditions on
    executions of this page may take as their acting steps (their parameter `acting`); not part of
    the bare framework.

    An interrupted reaction runs the node's code too, and its first `n` effects (sends among them)
    are applied, so it counts as acting. A delivery, completed (`deliver p e`) or interrupted
    (`crashDuring p (.deliver e) n`), is no acting step.

    Read aloud: at step `k`, `p` ticks, reacts to a protocol event, or crashes during one of the
    two. -/
def ActingStep {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (k : Nat) (p : Node) : Prop :=
  lbl x k = .tick p ∨ (∃ ev : Ev, lbl x k = .custom p ev) ∨
    (∃ n : Nat, lbl x k = .crashDuring p .tick n) ∨
    (∃ (ev : Ev) (n : Nat), lbl x k = .crashDuring p (.custom ev) n)

/-- Step `k` of `x` is `p`'s timer interrupt, a completed `tick p`. A reading of an execution that
    the conditions on executions of this page may take as their acting steps (their parameter
    `acting`); not part of the bare framework.

    It names fewer steps than `ActingStep`: `TickStep x k p` implies `x.ActingStep k p`,
    not the converse. A protocol event, and a reaction interrupted by a crash
    (`crashDuring p .tick n`, `crashDuring p (.custom ev) n`), are no `TickStep`. A network
    condition read at `TickStep` promises a delivery before each completed tick only.

    Read aloud: at step `k`, `p` ticks. -/
def TickStep {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (k : Nat) (p : Node) : Prop :=
  lbl x k = .tick p

/-- `p` is up in every configuration from `i` to `k`: outside the crashed set, with its local state
    known. A reading of an execution that the condition on executions `DeliveredBeforeActing` uses;
    not part of the bare framework, which defines no "up".

    A validator whose local state is known is not corrupted, so `p` is honest in each of these
    configurations; a validator that has not yet come online, or is crashed, in one of them is not
    up between `i` and `k`.

    Read aloud: in every configuration from `i` to `k`, `p` has come online, is not crashed, and is
    not corrupted. -/
def UpBetween {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (i k : Nat) (p : Node) : Prop :=
  ∀ l : Nat, i ≤ l → l ≤ k → p ∉ crashed x l ∧ state x l p ≠ none

/-- `p` is up and honest throughout the real window `[t, t']`: in every configuration the run is in
    somewhere between `t` and `t'` (left at `t` or later, entered at `t'` or earlier), `p` is
    outside the crashed set, its local state is known, and it is outside the corrupted set. A
    reading of an execution, not part of the bare framework (the condition on executions
    `SyncedWithinBy` reads `UpAndHonestUntilActing`).

    The configurations read are those in force at some real time of `[t, t']`, and those entered and
    left at one real time of it. The last conjunct follows from the second (a validator whose local
    state is known is not corrupted); it is written out so that the definition reads "up and
    honest".

    Read aloud: from the real time `t` to the real time `t'`, `p` is never crashed, never corrupted,
    and has come online. -/
def UpAndHonestThroughout {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (t t' : ℝ) (p : Node) : Prop :=
  ∀ i : Nat, t ≤ stamp x (i + 1) → stamp x i ≤ t' →
    p ∉ crashed x i ∧ state x i p ≠ none ∧ Honest x i p

/-- `p` is up and honest from the real time `t` until its first acting step at a real time at least
    `t'`: in every configuration the run is in at `t` or later (left at `t` or later), up to the one
    that acting step starts from (every such configuration, when `p` takes no acting step at a real
    time at least `t'`), `p` is outside the crashed set, its local state is known, and it is outside
    the corrupted set. `acting` is the reading of an execution that says which steps are acting
    steps: `ActingStep` (a tick, a protocol event, or a crash interrupting one of the two)
    or `TickStep` (a tick only), both on this page. A reading of an execution that the condition on
    executions `SyncedWithinBy` uses; not part of the bare framework.

    The window ends at `p`'s own acting step: nothing is asked of the configurations after it, also
    those entered at a real time at most `t'`. Beside `UpAndHonestThroughout t t' p`, which reads
    every configuration in force between `t` and `t'`.

    Read aloud: from the real time `t` until it acts at or after the real time `t'`, `p` is never
    crashed, never corrupted, and has come online. -/
def UpAndHonestUntilActing {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (acting : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev) → Nat → Node → Prop) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (t t' : ℝ) (p : Node) :
    Prop :=
  ∀ i : Nat, t ≤ stamp x (i + 1) →
    (∀ k : Nat, acting x k p → t' ≤ stamp x (k + 1) → i ≤ k) →
    p ∉ crashed x i ∧ state x i p ≠ none ∧ Honest x i p

/-- The deadline of a network synchronous from `tGST` on: `ΔDelay m` after the later of `t` and
    `tGST`, for a message `m` and the real time `t` the deadline counts from (a sending, a restart,
    a serving). `ΔDelay` is a delay per message, so that each kind of message may have its own.

    Read aloud: the delay of `m` after `t`, or after `tGST` if that is later. -/
def syncDeadline {Msg : Type} (tGST : ℝ) (ΔDelay : (m : Msg) → ℝ) (m : Msg) (t : ℝ) : ℝ :=
  max t tGST + ΔDelay m

/-- The deadline of a network synchronous from `tGST` on except during one asynchronous period
    `[tAsyncStart, tAsyncEnd)`: `syncDeadline tGST ΔDelay m t` when it is at most `tAsyncStart`;
    otherwise `ΔDelay m` after the latest of `t`, `tAsyncEnd` and `tGST`.

    Read aloud: a deadline that falls at the start of the period or before it stands; one that
    would fall later is counted from the end of the period instead, so nothing falls due inside the
    period. -/
noncomputable def deadlineOutside {Msg : Type} (tGST : ℝ) (ΔDelay : (m : Msg) → ℝ)
    (tAsyncStart tAsyncEnd : ℝ) (m : Msg) (t : ℝ) : ℝ :=
  if max t tGST + ΔDelay m ≤ tAsyncStart then max t tGST + ΔDelay m
  else max t (max tAsyncEnd tGST) + ΔDelay m

/-- The envelope `e` was put on the wire at step `i` and is **due** by the real time `t` under the
    deadline function `dl`: its deadline, read off its message and the real time of its sending, is
    at most `t`. Part of the conditions on executions `DeliveredBeforeActing` and
    `CatchUpAfterRestart`; the bare framework does not assume it.

    **The formula, clause by clause.**

    1. The sending.

           e ∈ x[i + 1].sent - x[i].sent

       Read aloud: there is one more copy of `e` in the sent envelopes of configuration `i + 1`
       than in those of configuration `i`, so step `i` put `e` on the wire.

    2. The deadline.

           dl e.msg (x.stamp (i + 1)) ≤ t

       Read aloud: the deadline of `e`'s message, counted from the real time of step `i`, is at
       most `t`.

    Read aloud: `e` was sent at step `i`, and its deadline has passed by the real time `t`. -/
def DueBy {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (dl : (m : Msg) → (tSend : ℝ) → ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) (i : Nat)
    (e : Envelope Node Msg) (t : ℝ) : Prop :=
  e ∈ sent x (i + 1) - sent x i ∧ dl e.msg (stamp x (i + 1)) ≤ t

/-- A condition on executions, which a statement takes as a hypothesis. Whenever a node `p` acts (at
    a step the reading `acting` names), every envelope addressed to `p` that was sent while `p` was
    up, with `p` up since, and whose deadline `dl` has passed, was delivered to `p` after that
    sending and before the acting step, with no memory-losing restart of `p` in between.

    `acting` is the reading of an execution that says which steps are acting steps:
    `ActingStep` (a tick, a protocol event, or a crash interrupting one of the two) or
    `TickStep` (a tick only), both on this page.

    **The formula, clause by clause.**

    1. An acting step of `p`.

           ∀ (k : Nat) (p : Node), acting x k p → …

       Read aloud: for every step `k` that `acting` names as an acting step of a node `p`; with
       `acting := Execution.ActingStep`, every step at which `p` ticks, reacts to a protocol event,
       or crashes during one of the two; with `acting := TickStep`, every step at which `p` ticks.

       Each of these steps is enabled only at a node that is up and honest, with its local state
       known and its clock existing, so the promise is made to such nodes. A corrupted validator
       takes none of them and is promised nothing.

    2. An envelope addressed to `p`, sent earlier, with `p` up since the sending.

           ∀ (i : Nat) (e : Envelope Node Msg), i < k → e.recipients.Has p → x.UpBetween i k p → …

       Read aloud: for every envelope `e` addressed to `p` and every step `i` before `k`, such that
       `p` has come online, is not crashed and is not corrupted in every configuration from `i` to
       `k`.

       So `p` is owed nothing here for an envelope sent while it was crashed or not yet online, or
       when it crashed after the sending: with no crash of `p` between `i` and `k` there is no
       restart either. What a node that restarted is owed is `CatchUpAfterRestart`, a separate
       condition. Promised to the recipients of the envelope only: a multicast owes nothing to a
       validator it was not addressed to.

    3. The deadline has passed by the acting step.

           DueBy dl x i e (x.stamp (k + 1)) → …

       Read aloud: step `i` put `e` on the wire, and its deadline `dl e.msg (x.stamp (i + 1))` is
       at most the real time of step `k`.

       The deadline is not strict: an acting step at exactly the deadline is owed the delivery.

    4. The delivery, after the sending, not voided since.

           ∃ j : Nat, i < j ∧ j < k ∧ x.lbl j = .deliver p e ∧
             ∀ l : Nat, j < l → l < k → x.lbl l ≠ .restart p false

       Read aloud: some step `j` after the sending `i` and before `k` delivers `e` to `p`, and no
       step strictly between `j` and `k` restarts `p` with its memory lost.

       The delivery comes after the copy's own sending: each copy of `e` put on the wire is owed a
       delivery of its own, and a delivery of an earlier copy of the same envelope, at a step before
       `i`, does not count for the copy sent at `i`. It is stated over delivery steps, not over
       `p`'s view: a restart keeps the view, so "the message is in `p`'s view at `k`" would already
       hold for a validator that received it before a reboot and lost it with its memory. An
       interrupted delivery, `crashDuring p (.deliver e) n`, is no `deliver p e` step and counts as
       no delivery.

    The condition `i < k` matters only when a deadline may be at most the real time of the sending:
    otherwise an envelope put on the wire at or after step `k` is due after the real time of step
    `k`. `DeliveredBeforeActing acting (syncDeadline tGST ΔDelay) x` is the network synchronous from
    `tGST` on, `DeliveredBeforeActing acting (deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd) x`
    the same network except during the asynchronous period `[tAsyncStart, tAsyncEnd)`.

    Read aloud: whenever an honest node acts at a step `acting` names, every envelope addressed to
    it that was sent while it was up, with the node up since, and whose deadline has passed, was
    delivered to it after that sending and before acting, with no memory-losing restart in between. -/
def DeliveredBeforeActing {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (acting : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev) → Nat → Node → Prop) (dl : (m : Msg) → (tSend : ℝ) → ℝ)
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (k : Nat) (p : Node), acting x k p →
    ∀ (i : Nat) (e : Envelope Node Msg), i < k → e.recipients.Has p → UpBetween x i k p →
      DueBy dl x i e (stamp x (k + 1)) →
      ∃ j : Nat, i < j ∧ j < k ∧ lbl x j = .deliver p e ∧
        ∀ l : Nat, j < l → l < k → lbl x l ≠ .restart p false

/-- A condition on executions, which a statement takes as a hypothesis. Whenever a node `p` acts (at
    a step the reading `acting` names), every envelope addressed to `p` and sent before some restart
    of `p` was delivered to `p` again after its last restart, once its deadline `dl` from the
    sending and the deadline `dlW` from every restart of `p` since the sending have passed.

    `acting` is the reading of an execution that says which steps are acting steps:
    `ActingStep` (a tick, a protocol event, or a crash interrupting one of the two) or
    `TickStep` (a tick only), both on this page.

    **The formula, clause by clause.**

    1. An acting step of `p`, and an envelope addressed to `p`, sent earlier.

           ∀ (k : Nat) (p : Node), acting x k p →
             ∀ (i : Nat) (e : Envelope Node Msg), i < k → e.recipients.Has p → …

       Read aloud: for every step `k` that `acting` names as an acting step of a node `p`, and
       every envelope `e` addressed to `p` and every step `i` before `k`.

    2. A restart of `p` since the sending.

           (∃ (l : Nat) (keep : Bool), i < l ∧ l < k ∧ x.lbl l = .restart p keep) → …

       Read aloud: some step strictly between `i` and `k` restarts `p`, with its memory kept or
       lost.

       The restart that brings `p` online for the first time counts as a restart: a validator that
       comes online after an envelope addressed to it was sent is owed it, `dlW` after it came
       online.

    3. The deadline from the sending has passed.

           DueBy dl x i e (x.stamp (k + 1)) → …

       Read aloud: step `i` put `e` on the wire, and its deadline `dl e.msg (x.stamp (i + 1))` is
       at most the real time of step `k`.

    4. The deadline from every restart since the sending has passed.

           (∀ (l : Nat) (keep : Bool), i < l → l < k → x.lbl l = .restart p keep →
             dlW e.msg (x.stamp (l + 1)) ≤ x.stamp (k + 1)) → …

       Read aloud: for every step `l` strictly between `i` and `k` that restarts `p`, the deadline
       of `e`'s message counted from the real time of step `l` is at most the real time of step
       `k`.

       Stated for every such restart rather than for the last one: when `dlW` grows with the real
       time it counts from, as `syncDeadline` and `deadlineOutside` do, the last restart's deadline
       is the largest, since the real time is monotone along an execution (`ObservedRun.mono`), and
       the two readings agree.

    5. The delivery, after the last restart.

           ∃ j : Nat, j < k ∧ x.lbl j = .deliver p e ∧
             ∀ (l : Nat) (keep : Bool), j < l → l < k → x.lbl l ≠ .restart p keep

       Read aloud: some step `j` before `k` delivers `e` to `p`, and no step strictly between `j`
       and `k` restarts `p`, with its memory kept or lost.

       So a node that restarted is owed again what it was delivered before the restart, whether
       its memory was kept or lost: a delivery made before a restart may have been rejected by the
       node (a block ahead of its clock), and then the node does not hold it after the restart.

    This is a push of every earlier envelope to a node that restarted, which a network that does not
    keep a backlog per recipient does not give; a protocol whose nodes fetch what they missed states
    `SyncedWithinBy` instead. `DeliveredBeforeActing acting dl x` and
    `CatchUpAfterRestart acting dl dlW x` together owe every envelope addressed to a node that acts
    at a step `acting` names, sent before that step, whose deadline from the sending has passed and,
    when the node restarted since, whose deadline from each such restart has passed.

    Read aloud: whenever an honest node acts at a step `acting` names, every envelope addressed to
    it that was sent before one of its restarts was delivered to it again after its last restart
    before acting, once both the deadline from the sending and the deadline from each of its
    restarts since have passed. -/
def CatchUpAfterRestart {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (acting : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev) → Nat → Node → Prop) (dl : (m : Msg) → (tSend : ℝ) → ℝ)
    (dlW : (m : Msg) → (tRestart : ℝ) → ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (k : Nat) (p : Node), acting x k p →
    ∀ (i : Nat) (e : Envelope Node Msg), i < k → e.recipients.Has p →
      (∃ (l : Nat) (keep : Bool), i < l ∧ l < k ∧ lbl x l = .restart p keep) →
      DueBy dl x i e (stamp x (k + 1)) →
      (∀ (l : Nat) (keep : Bool), i < l → l < k → lbl x l = .restart p keep →
        dlW e.msg (stamp x (l + 1)) ≤ stamp x (k + 1)) →
      ∃ j : Nat, j < k ∧ lbl x j = .deliver p e ∧
        ∀ (l : Nat) (keep : Bool), j < l → l < k → lbl x l ≠ .restart p keep

/-- A condition on executions, which a statement takes as a hypothesis. What an honest node that is
    up serves, at a real time `t`, to a peer that asks either is already served by every node up and
    honest from `t` until it acts at or after the sync deadline `sync m t`, or reaches that node by
    that deadline, before that node acts at or after it, at a step after which that node stays up
    and honest until that acting step.

    `serves tClock l m` is the protocol's selection: a node whose clock reads `tClock` and whose
    value is `l` serves `m` to a peer that asks. It reads the node's clock and value, not the real
    time. `acting` is the reading of an execution that says which steps are acting
    steps: `ActingStep` (a tick, a protocol event, or a crash interrupting one of the two)
    or `TickStep` (a tick only), both on this page.

    **The formula, clause by clause.**

    1. A holder `p` serving `m` at the real time `t`.

           ∀ (t : ℝ) (i : Nat) (p p' : Node) (m : Msg) (tClock : Time) (l : Local Node Msg NodeState),
             x.InForce i t → p ∉ x[i].crashed → x.Honest i p → x[i][p] = some l →
             x[i].clock p = some tClock → serves tClock l.st m → …

       Read aloud: for every real time `t`, the configuration `i` in force at `t`, and every node
       `p` that is not crashed and not corrupted there, whose local state there is `l` and whose
       clock there reads `tClock`, and that serves `m` from them.

       The configuration in force at `t` is the last one entered before `t`, so the holder's state
       is the one it had just before `t`.

    2. A receiver `p'` up and honest from `t` until it acts at or after the deadline.

           x.UpAndHonestUntilActing acting t (sync m t) p' → …

       Read aloud: `p'` is up and honest in every configuration the run is in from `t` on, up to
       the one its first acting step at a real time at least `sync m t` starts from.

    3. Either the receiver already serves `m` itself.

           (∃ (tClock'' : Time) (l'' : Local Node Msg NodeState),
             x[i][p'] = some l'' ∧ x[i].clock p' = some tClock'' ∧ serves tClock'' l''.st m) ∨ …

       Read aloud: in the configuration `i` in force at `t`, `p'`'s local state `l''` and clock
       reading `tClock''` serve `m`: `p'` already has `m`, and nothing has to reach it.

    4. Or a step from which `p` already served `m`.

           ∃ (j i' : Nat) (e : Envelope Node Msg) (tClock' : Time) (l' : Local Node Msg NodeState),
             i' ≤ j ∧ x.stamp i' < t ∧ x[i'][p] = some l' ∧ x[i'].clock p = some tClock' ∧
             serves tClock' l'.st m ∧ …

       Read aloud: some configuration `i'`, entered before `t` and no later than step `j`, has
       `p`'s local state `l'` and clock reading `tClock'`, from which `p` serves `m`.

    5. The delivery, by the deadline.

           x.lbl j = .deliver p' e ∧ e.sender = p ∧ e.msg = m ∧ x.stamp (j + 1) ≤ sync m t ∧ …

       Read aloud: step `j` delivers to `p'` an envelope from `p` carrying `m`, at a real time at
       most `sync m t`.

    6. Before `p'` acts at or after the deadline.

           (∀ k : Nat, acting x k p' → sync m t ≤ x.stamp (k + 1) → j < k) ∧ …

       Read aloud: every step of `p'` that `acting` names, taken at a real time at or after
       `sync m t`, comes after step `j`.

    7. The receiver stays up and honest from the delivery until it acts at or after the deadline.

           ∀ n : Nat, j ≤ n → (∀ k : Nat, acting x k p' → sync m t ≤ x.stamp (k + 1) → n ≤ k) →
             p' ∉ x[n].crashed ∧ x[n][p'] ≠ none ∧ x.Honest n p'

       Read aloud: in every configuration from step `j`'s on, up to the one `p'`'s first acting step
       at a real time at least `sync m t` starts from, `p'` is not crashed, has come online and is
       not corrupted (the three conjuncts of `UpAndHonestUntilActing`). A delivery to a node that
       crashes before that acting step is not the one this condition names.

    `SyncedWithinBy acting serves (syncDeadline tGST ΔSync) x` is the assumption on a network
    synchronous from `tGST` on,
    `SyncedWithinBy acting serves (deadlineOutside tGST ΔSync tAsyncStart tAsyncEnd) x` on the same
    network except during the asynchronous period.

    The receiver is read up to its own first acting step at or after the deadline: a node that
    crashes right after that step is still owed the delivery, and nothing is asked of it after.

    Read aloud: what an honest node that is up serves at a real time `t`, every node up and honest
    from `t` until it acts at or after the sync deadline either already serves itself at `t`, or is
    delivered by that deadline, before it acts at or after the deadline, at a step after which it
    stays up and honest until that acting step, and the delivery comes no earlier than a state in
    which the holder served it. -/
def SyncedWithinBy {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (acting : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev) → Nat → Node → Prop)
    (serves : (tClock : Time) → (l : L) → (m : Msg) → Prop) (sync : (m : Msg) → (t : ℝ) → ℝ) (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev))
    : Prop :=
  ∀ (t : ℝ) (i : Nat) (p p' : Node) (m : Msg) (tClock : Time) (l : L),
    InForce x i t → p ∉ crashed x i → Honest x i p → state x i p = some l →
    clock x i p = some tClock → serves tClock l m →
    UpAndHonestUntilActing acting x t (sync m t) p' →
    (∃ (tClock'' : Time) (l'' : L),
      state x i p' = some l'' ∧ clock x i p' = some tClock'' ∧ serves tClock'' l'' m) ∨
    ∃ (j i' : Nat) (e : Envelope Node Msg) (tClock' : Time) (l' : L),
      i' ≤ j ∧ stamp x i' < t ∧ state x i' p = some l' ∧ clock x i' p = some tClock' ∧
      serves tClock' l' m ∧
      lbl x j = .deliver p' e ∧ e.sender = p ∧ e.msg = m ∧ stamp x (j + 1) ≤ sync m t ∧
      (∀ k : Nat, acting x k p' → sync m t ≤ stamp x (k + 1) → j < k) ∧
      (∀ n : Nat, j ≤ n → (∀ k : Nat, acting x k p' → sync m t ≤ stamp x (k + 1) → n ≤ k) →
        p' ∉ crashed x n ∧ state x n p' ≠ none ∧ Honest x n p')

/-! ### Ticks and the adversary's sends

Two conditions on executions: `TickOncePerReading`, at most one tick of a node at each reading of
its clock, and `UnforgeableSends`, the adversary's half of unforgeability. -/

/-- A condition on executions, which a statement takes as a hypothesis. A node takes at most one
    tick at each reading of its clock.

    **The formula, clause by clause.**

    1. Two ticks of `p`, each taken while `p`'s clock reads `t`.

           ∀ (i j : Nat) (p : Node) (t : Time), x.lbl i = .tick p → x[i].clock p = some t →
             x.lbl j = .tick p → x[j].clock p = some t → …

       Read aloud: for every two steps `i` and `j` that are `p`'s timer interrupt, taken from
       configurations in which `p`'s clock reads `t`.

    2. They are one step.

           i = j

       Read aloud: steps `i` and `j` are the same step.

    The step relation allows any number of ticks at one reading (`nodeSpec`): a tick changes no
    clock. A reaction interrupted by a crash (`crashDuring p .tick n`) is no `tick p` step, and
    counts as no tick here.

    Read aloud: a node ticks at most once while its clock shows any one reading. -/
def TickOncePerReading {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (i j : Nat) (p : Node) (t : Time), lbl x i = .tick p → clock x i p = some t →
    lbl x j = .tick p → clock x j p = some t → i = j

/-- A condition on executions, which a statement takes as a hypothesis. At every step that is
    neither a tick nor a delivery, each envelope put on the wire is a copy of a signed message
    already on it, or is signed by a corrupted validator and forges no honest validator: neither its
    message's object nor any object that object includes, when attributed to a validator honest at
    that step, is new on the wire. Who an object is attributed to, `author`, and what it includes,
    `carries`, are the protocol's, passed as parameters.

    The steps bound are those that put envelopes on the wire without being a tick or a delivery: an
    `adversarial` step, a protocol event (`custom`), and a reaction interrupted by a crash
    (`crashDuring`); the other steps of that kind put nothing on the wire. The adversary's half of
    unforgeability; the other half, that the ticks and deliveries of honest validators forge
    nothing, is the protocol's.

    **The formula, clause by clause.**

    1. A step `i` that is neither a tick nor a delivery, and an envelope `e` it puts on the wire.

           ∀ (i : Nat) (e : Envelope Node Msg), (∀ p : Node, x.lbl i ≠ .tick p) →
             (∀ (p : Node) (e' : Envelope Node Msg), x.lbl i ≠ .deliver p e') →
             e ∈ x[i + 1].sent - x[i].sent → …

       Read aloud: for every step `i` that is no node's timer interrupt and no delivery, and every
       envelope `e` of which configuration `i + 1` has one more copy in its sent envelopes than
       configuration `i`.

    2. A copy.

           (∃ e' ∈ x[i].sent, e'.toSignedMsg = e.toSignedMsg) ∨ …

       Read aloud: some envelope already on the wire before the step carries `e`'s signed message
       (its signer and its message).

    3. Or the adversary's own envelope, forging nothing.

           e.sender ∈ x[i].adv ∧
             ∀ (mObject : Msg) (v : Node), (mObject = e.msg ∨ carries e.msg mObject) →
               author mObject = some v → x.Honest i v →
               ∃ e' ∈ x[i].sent, e'.msg = mObject ∨ carries e'.msg mObject

       Read aloud: `e`'s signer is corrupted before the step, and every object that `e`'s message is
       or includes, attributed to a validator honest before the step, is on the wire before the
       step: some envelope there has it as its message's object, or has a message that includes it.

    Read aloud: the adversary sends no honest validator's object that was not already sent. -/
def UnforgeableSends {Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (author : (m : Msg) → Option Node) (carries : (m : Msg) → (m' : Msg) → Prop)
    (x : ObservedRun (ObservedConfig Node Msg L) (Action Node Msg Ev)) : Prop :=
  ∀ (i : Nat) (e : Envelope Node Msg), (∀ p : Node, lbl x i ≠ .tick p) →
    (∀ (p : Node) (e' : Envelope Node Msg), lbl x i ≠ .deliver p e') →
    e ∈ sent x (i + 1) - sent x i →
    (∃ e' ∈ sent x i, e'.toSignedMsg = e.toSignedMsg) ∨
      (e.sender ∈ adv x i ∧
        ∀ (mObject : Msg) (v : Node),
          (mObject = e.msg ∨ carries e.msg mObject) →
          author mObject = some v → Honest x i v →
          ∃ e' ∈ sent x i, e'.msg = mObject ∨ carries e'.msg mObject)

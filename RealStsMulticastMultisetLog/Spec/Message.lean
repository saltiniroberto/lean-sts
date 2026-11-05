module
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Int.Interval

@[expose] public section

/-!
# Time, messages, views

Vocabulary shared by every model. Nothing here commits to a network model, an
adversary, or a protocol.
-/

set_option autoImplicit false

namespace Framework.RealStsMulticastMultisetLog

/-- A node's clock reading, an integer — Majorum §Model has "time is divided into
    discrete rounds", TOB-SVD counts time steps.

    `Config.clock p` is the node `p`'s reading (`none` before its clock exists, and from `p`'s
    corruption on), and it is what
    a protocol is handed. The real time is
    not measured in this: it is a real number, the execution's `Execution.stamp`, read only by the
    conditions on executions. The clocks are digital; the steps that set them happen at real
    times.

    Slots are deliberately absent: Majorum's `4Δ`-round slot is a property of
    that model, and it defines its own `proposing`/`voting` rounds over `Time`
    (see `Models.Majorum`). TOB-SVD has no round-aligned slots at all.

    **Notation, not an `abbrev`.** Measured twice in this repository now: `omega` does
    not see through a reducible alias, so `abbrev Time := Nat` makes arithmetic on
    rounds unprovable by it. Notation expands at parse time, leaving nothing to hide
    the `Nat`.

    Read aloud: a clock reading is a natural number. -/
scoped notation "Time" => Nat

/-- A message together with its signer. Signing is structural: appearing under
    `sender = p` *is* being signed by `p`. -/
structure SignedMsg (Node Msg : Type) where
  /-- The signer. -/
  sender : Node
  /-- The message. -/
  msg : Msg
  deriving DecidableEq

/-- A validator's view: every message it has received so far (Majorum's `V^r_i`,
    TOB-SVD's received-message state). Maintained by the framework, so a
    protocol can neither forget nor fabricate a delivery. -/
abbrev View (Node Msg : Type) := Finset (SignedMsg Node Msg)

/-- Whom a send is addressed to: every validator (a broadcast), or the validators of a
    set (a multicast; a singleton is a point-to-point send). `all` is not `only univ` so
    that a broadcast needs no `Fintype Node`. -/
inductive Recipients (Node : Type) where
  /-- Every validator. -/
  | all
  /-- The validators of `nodes`. -/
  | only (nodes : Finset Node)
  deriving DecidableEq

/-- `r.Has p`: `p` is among the recipients `r`. -/
def Recipients.Has {Node : Type} (r : Recipients Node) (p : Node) : Prop :=
  match r with
  | .all => True
  | .only nodes => p ∈ nodes

/-- What a node's reaction sends: a message with its recipients. Unsigned: the signature is
    the reacting node's, added when the reaction is applied (`applyNodeStepResult`). -/
structure Addressed (Node Msg : Type) where
  /-- The message. -/
  msg : Msg
  /-- Its recipients. -/
  recipients : Recipients Node
  deriving DecidableEq

/-- A signed message with its recipients: what the network holds in the sent log. A
    delivery to `p` takes the signed message out of it; the recipients decide whether `p`
    may be delivered it, and reach no view. -/
structure Envelope (Node Msg : Type) extends SignedMsg Node Msg where
  /-- The recipients. -/
  recipients : Recipients Node
  deriving DecidableEq

/-- `a.sign p`: the envelope of the addressed message `a` signed by `p`. -/
def Addressed.sign {Node Msg : Type} (a : Addressed Node Msg) (p : Node) : Envelope Node Msg :=
  { sender := p, msg := a.msg, recipients := a.recipients }

end Framework.RealStsMulticastMultisetLog

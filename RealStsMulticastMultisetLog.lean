module
public import RealStsMulticastMultisetLog.Spec.Message
public import RealStsMulticastMultisetLog.Spec.Protocol
public import RealStsMulticastMultisetLog.Spec.Execution
public import RealStsMulticastMultisetLog.Spec.ValidatorSets
public import RealStsMulticastMultisetLog.Spec.Conditions

@[expose] public section

/-!
# The sts variant in real time, its clock advanced by a step of its own — the root module

A copy of `RStsVariant`'s specification pages (`experiments/r-sts-variant/RStsVariant/Spec/`, taken
2026-10-28 at `dev` `650afe543`) into the namespace `RealStsMulticastMultisetLog`, changed so that a node's clock
advances by an environment step of its own, `setClock`, which runs no protocol code and is taken
whether the node is up or crashed. Every other node event runs the protocol at the stored reading, and a
restart leaves the clock as it is. Since 29 Oct 2026 a validator's local state may be unknown
(before it first comes online, and from its corruption on), and its clock, a configuration field of
its own, does not exist at the start; a restart needs the clock, so a validator's clock starts
before it first comes online; and a corruption empties the validator's clock as well as its local
state, and no `setClock` is taken at a corrupted validator. `experiments/r-sts-variant-2/CHANGES.md`
lists every change and why. `RStsVariant` is not edited.
-/

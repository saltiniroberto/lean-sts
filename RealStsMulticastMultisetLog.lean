module
public import RealStsMulticastMultisetLog.Spec.Message
public import RealStsMulticastMultisetLog.Spec.Protocol
public import RealStsMulticastMultisetLog.Spec.Execution
public import RealStsMulticastMultisetLog.Spec.ValidatorSets
public import RealStsMulticastMultisetLog.Spec.Conditions

@[expose] public section

/-!
# A framework for message-passing distributed protocols — real time, multicast multiset log

**The suggested flavour.** A configuration carries no time: each configuration of an execution is
entered at a real time, the execution's `Execution.stamp`. Each node's clock is a natural-number
reading moved only by an environment step of its own, `setClock`, which runs no protocol code and is
taken at a node that is not corrupted, whether it is up or crashed; every other node event (a tick,
a delivery, a protocol event, a restart) runs at the reading the clock holds. A validator's local
state is unknown before it first comes online and from its corruption on, and its clock exists from
its first `setClock` until its corruption; a restart needs the clock. Sends are multicast: each
names its recipients, and the log of sent envelopes is a `Multiset`. How readings relate to the real
time, when ticks and deliveries must happen, and every other timing assumption are conditions on
executions, which statements take as hypotheses.

`Spec/` states the model (`Message`, `Protocol`, `Execution`, `Observable`, `ValidatorSets`,
`Conditions`), and this module imports it; `Analysis/` proves things about it, and is imported
page by page.
-/

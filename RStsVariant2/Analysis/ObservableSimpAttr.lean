module
public import Lean

@[expose] public section

/-!
# The simp set `observable_exec`

Registers the simp attribute `observable_exec`, whose lemmas (`RStsVariant2.Analysis.Observable`)
rewrite each reading of the class `Observable` (`RStsVariant2.Spec.Observable`) at a run of a
protocol to the run's own: `Observable.stamp x i` to `x.stamp i`, `Observable.clock x i p` to
`x[i].clock p`, and so on. The attribute is registered on a page of its own because a page cannot
use an attribute it registers. Not part of the bare framework, and no condition on executions.
-/

/-- The lemmas that rewrite each reading of `Observable` at a run of a protocol to the run's own
    (`RStsVariant2.Analysis.Observable`). -/
register_simp_attr observable_exec

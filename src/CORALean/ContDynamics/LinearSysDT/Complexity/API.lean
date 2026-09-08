import CORALean.ContDynamics.LinearSysDT.Complexity.ReachError

/-!
# How large `LinearSysDT`'s computed sets are

`reachError`'s generator count, proved: the one fact `reach_order_le` does not
already give, since `reachError` is not reduced and so is not covered by the
same argument. `reach`'s own bound stays in `Theorems/ReachOrderLe.lean`,
beside `ReachOrderLeConZonotope.lean` and the guarantees it is proved for; it
is not restated here.
-/

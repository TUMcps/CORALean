import CORALean.HybridDynamics.Complexity.Time.Jump
import CORALean.HybridDynamics.Complexity.Time.JumpIntersection

/-!
# What a hybrid automaton's discrete step costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `jumpCost` prices `jump` and `jumpOfPoint` —
one `mtimes`, one `plus`, one embedded point — at what those three cost, a
parameter no representation-agnostic file can fix. `jumpIntersectionCost` adds
the guard cut ahead of that.

`TimeIntervalStep` and its two siblings are **not** counted here: they run the
continuous flow, `LinearSys.timeIntervalStep`, a Taylor-order enclosure this
issue's own notes mark as blocked on another one. A hybrid automaton's *jump*
is what is discrete and priced here; its *stay* is not.
-/

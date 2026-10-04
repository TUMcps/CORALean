import CORALean.ContDynamics.Conform.Definitions.API
import CORALean.ContDynamics.Conform.Plant
import CORALean.ContDynamics.Conform.Theorems.API

/-!
# Reachset conformance, collected

CORA's `conform` and `isconform`: whether the measurements of a real system lie in the
reachable outputs of its model, and the linear and quadratic programs that identify
uncertainty sets making them so. Over ℝ and with no float layer — the programs are a
solver's, and what is proved is what any feasible point of them guarantees.
-/

import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.API

/-!
# Enclosing a matrix exponential, collected

What a discretization needs and nothing else uses: `e^{AΔt}` is transcendental,
so a step is taken against an interval matrix around it rather than against it.

Enclosures only, no representation — an interval matrix is `Interval (Mat ℝ m n)`
like any other set.
-/

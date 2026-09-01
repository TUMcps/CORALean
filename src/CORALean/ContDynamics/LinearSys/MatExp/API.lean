import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.API

/-!
# Enclosing a matrix exponential, collected

What a discretization needs and nothing else uses: `e^{AΔt}` is transcendental,
so a step is taken against an interval matrix around it rather than against it.
The enclosures are in `Enclosures`, their guarantees in `Theorems`.

An interval matrix is `Interval (Mat ℝ m n)`, a set representation like any
other, so nothing here declares one — this directory holds the *enclosures*, not
a representation.
-/

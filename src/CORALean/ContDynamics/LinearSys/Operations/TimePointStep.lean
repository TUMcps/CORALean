import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContSet.Interval.Real.Instances

/-!
# One step of the flow, at its end rather than over it

CORA's `Rhom_tp ⊕ Rpar`: the initial set carried by `e^{Ar}` exactly, and what
the input contributes over the step. The counterpart of `timeIntervalStep`,
which covers the whole of `[0, r]` and pays a convex hull for it; here nothing
is interpolated, so the only enclosure is `inputSolution`'s.

This is the step `discretize` hands `LinearSysDT` — the same two operands, named
once so that a guarantee about one step can be stated without a discretization
around it. `timePointStep_outer` is the enclosure and
`timePointStep_subset_reach_add_error` the reverse, which is where the naming
earns itself.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about this definition must make the same one — the `l∞` operator
norm — or the terms will not match.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state at the end of a step: `e^{Ar} X₀ ⊕ inputSolution`. -/
noncomputable def LinearSys.timePointStep (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ U : S n) : S n :=
  Mtimes.mtimes (exp (r • toRealMat sys.A)) X₀ ⊞ sys.inputSolution r η U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

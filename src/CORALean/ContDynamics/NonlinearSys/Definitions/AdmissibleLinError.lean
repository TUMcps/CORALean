import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The admissible linearization error of an expansion vector

[1, Eq. 7]: the bound `L̄ := |(e^{Ar} - I)⁻¹ A| θ r` a linearization error must stay
under, so that the set `R̄err(r) = A⁻¹(e^{Ar} - I)[-L̂, L̂]` it drives stays inside
`[-θ r, θ r]`, the paper's eq. (6). `θ` is the user's expansion vector.

One `let` per printed factor: `M` is the matrix the paper multiplies (6) by, and
the absolute value is entrywise, as the paper says. `r • θ` is the paper's `θ · r`.

The paper's claim that `L̂ ≤ L̄` suffices is false in two dimensions;
`Theorems/AdmissibleLinErrorNotSufficient.lean` has the counterexample and
`Theorems/ErrReachSubsetOfAbsLe.lean` the condition that does suffice.

Real only: a specification, built from `exp` and a matrix inverse, with nothing
to round.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L̄ = |(e^{Ar} - I)⁻¹ A| θ r` of [1, Eq. 7], at the step `r` and expansion vector `θ`. -/
noncomputable def NonlinearSys.admissibleLinError (A : Mat ℝ n n) (r : ℝ) (θ : Vec ℝ n) :
    Vec ℝ n :=
  let M : Mat ℝ n n := (NormedSpace.exp (r • A) - 1)⁻¹ * A
  Real.MatExp.absMat M *ᵥ (r • θ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

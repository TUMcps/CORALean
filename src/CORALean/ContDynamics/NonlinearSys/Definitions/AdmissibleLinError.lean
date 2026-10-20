module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The admissible linearization error of an expansion vector

[1, Eq. 7]: the bound `L̄ := |(e^{Ar} - I)⁻¹ A| θ r` a linearization error must stay under, so that
the set `R̄err(r) = A⁻¹(e^{Ar} - I)[-L̂, L̂]` it drives stays inside `[-θ r, θ r]`, the paper's
eq. (6). `θ` is the user's expansion vector; the absolute value is entrywise, and `r • θ` is the
paper's `θ · r`. The paper's claim that `L̂ ≤ L̄` suffices is false in two dimensions;
`Theorems/AdmissibleLinErrorNotSufficient.lean` has the counterexample and
`Theorems/ErrReachSubsetOfAbsLe.lean` the condition that does suffice. Real only: a
specification, built from `exp` and a matrix inverse, with nothing to round.

## Inputs
* `A` – system matrix
* `r` – step size
* `θ` – expansion vector

## Output
* the admissible linearization error bound

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

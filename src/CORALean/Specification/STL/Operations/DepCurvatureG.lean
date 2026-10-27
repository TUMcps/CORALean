module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The interval matrix `G` of the curvature set

[1, Eq. 14-20]: `G = T^(κ+1) ⊕ E Δt`, with `T^(o)` and `E` as in `STL.depCurvatureF`: the terms
`[c_j Δt^j, 0] A^{j-1}/j!` for `j = 2, ..., κ+1`, entry by entry as `MatExp.constCorrTerm`
(whose index `i` is `j - 2`), widened by `[-E, E] Δt`.

Real-only, a specification: the sets and matrices are real; the rounded refinement is
`STL.depCurvatureGFloat`.

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `κ` – Taylor order

## Output
* the interval matrix of the input curvature set

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: `G = T^(κ+1) ⊕ E Δt`. -/
noncomputable def STL.depCurvatureG (A : Mat ℝ n n) (Δt : ℝ) (κ : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range κ, min (MatExp.constCorrTerm A Δt i j k) 0)
    - Δt * MatExp.expRemainderMat A Δt κ j k
  sup := fun j k => (∑ i ∈ Finset.range κ, max (MatExp.constCorrTerm A Δt i j k) 0)
    + Δt * MatExp.expRemainderMat A Δt κ j k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Specification.STL.Operations.DepCurvatureG

@[expose] public section

/-!
# The interval matrix `G` of the curvature set, over floats

[1, Eq. 14-20]: `G = T^(κ+1) ⊕ E Δt`, with the terms `[c_j Δt^j, 0] A^{j-1}/j!` for
`j = 2, ..., κ+1`. Each term is the box of `MatExp.intervalConstCorrTerm` at the point box `A`, the
sums are rounded outward, and the remainder is the scalar float bound `Δt · expRemainderBound` at
the norm bound of `Δt A`, where the exact layer takes the entries of the remainder matrix. Soundness
is `STL.depCurvatureGFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `κ` – Taylor order

## Output
* the float interval matrix of the input curvature set
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: `G = T^(κ+1) ⊕ E Δt`, rounded outward. -/
def STL.depCurvatureGFloat (A : Mat 𝕋 n n) (Δt : 𝕋) (κ : ℕ) : Interval (Mat 𝕋 n n) :=
  MatExp.intervalConstCorrectionMatrix (Interval.point A) Δt κ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

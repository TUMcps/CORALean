module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Specification.STL.Operations.DepCurvatureF

@[expose] public section

/-!
# The interval matrix `F` of the curvature set, over floats

[1, Eq. 14-20]: `F = T^(κ) A ⊕ E` with `[c_j Δt^j, 0] A^j/j!` the term of order `j`, summed from
order two, and `E = [-E, E]` the remainder. Each term is the box of `MatExp.intervalCorrTerm` at the
point box `A`, the sums are rounded outward, and the remainder is the scalar float bound
`expRemainderBound` at the norm bound of `Δt A`, where the exact layer takes the entries of the
remainder matrix `E`: wider by the gap between an entry and the norm. Soundness is
`STL.depCurvatureFFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `κ` – Taylor order

## Output
* the float interval matrix of the curvature set
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

/-- [1, Eq. 14-20]: `F = T^(κ) A ⊕ E`, rounded outward. -/
def STL.depCurvatureFFloat (A : Mat 𝕋 n n) (Δt : 𝕋) (κ : ℕ) : Interval (Mat 𝕋 n n) :=
  MatExp.intervalCorrectionMatrix (Interval.point A) Δt κ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

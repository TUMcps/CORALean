import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Alg. 2` line 3: the curvature radius `μ`

`maxBackReachMu`: [1, Alg. 2] line 3, `μ ← √γ ‖(e^{AΔt} - I_n)G‖`, at the Frobenius norm,
which dominates (22)'s spectral one; `G` and `γ` come from `box(X_end)`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 3: `μ ← √γ ‖(e^{AΔt} - I_n)G‖`, at the Frobenius norm, which dominates
(22)'s spectral one; `G` and `γ` come from `box(X_end)`. -/
noncomputable def LinearSys.maxBackReachMu (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (B : Zonotope (Vec ℝ n)) : ℝ :=
  Real.sqrt B.h
    * Real.sqrt (∑ j, ∑ i, ((exp (Δt • toRealMat sys.A) - 1) *ᵥ B.G j) i ^ 2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

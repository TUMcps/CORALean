import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Real.Instances
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# `Alg. 2` line 3: the curvature radius `μ`

`maxBackReachMu`: [1, Alg. 2] line 3, `μ ← √γ ‖(e^{AΔt} - I_n)G‖₂`, (22) as printed: `‖·‖₂` is
the spectral norm, the operator norm between Euclidean spaces (Mathlib's
`Matrix.instL2OpNormedAddCommGroup`, named explicitly since the tree's matrices otherwise carry
the ℓ^∞ one), and `G ∈ ℝ^{n×γ}` is the generator matrix of `box(X_end)`, its columns the
zonotope's generators.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 3: `μ ← √γ ‖(e^{AΔt} - I_n)G‖₂` at the spectral norm, `G` and `γ` from
`box(X_end)`. -/
noncomputable def LinearSys.maxBackReachMu (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (B : Zonotope (Vec ℝ n)) : ℝ :=
  let G : Matrix (Fin n) (Fin B.h) ℝ := Matrix.of fun i j => B.G j i   -- G from box(X_end)
  let γ := B.h                                                           -- γ, its columns
  Real.sqrt γ * (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℝ)).toNorm.norm
    ((exp (Δt • toRealMat sys.A) - 1) * G)                               -- √γ ‖(e^{AΔt} - I)G‖₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

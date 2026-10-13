import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfExpMulVec
import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ProbZonotope.Real.Definitions.Eph
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# The hull's value of a point under the linear flow

`[1, Prop. 3]` for the G-zonotope with uncertain mean `𝒵 = (c, g, Σ)`: the enclosing
probabilistic hull of `e^{At} 𝒵` at `x' = e^{At} x` is `e^{-tr(A)t}` times the hull of `𝒵` at
`x`. The hull is the supremum of the Gaussian density over the means `μ ∈ Z`, which `e^{At}`
maps onto the means of `e^{At} Z`, and `gaussPdf_exp_mulVec` scales each density. The
supremum scales with the nonnegative factor `e^{-tr(A)t}`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open WithLp Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.eph_mtimes_exp (P : ProbZonotope n) (hP : 0 < P.cov.det) (A : Mat ℝ n n)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (P.mtimes (exp (t • A))).eph (toLp 2 (exp (t • A) *ᵥ ofLp x))
      = Real.exp (-(t * A.trace)) * P.eph x := by -- --- PROOF ---
  unfold ProbZonotope.eph
  rw [ProbZonotope.mtimes, ← Zonotope.mtimes_exact]
  rw [Set.image_image]
  -- each density is scaled by `e^{-tr(A)t}`
  have himg : (fun μ => gaussPdf (exp (t • A) *ᵥ μ) (exp (t • A) * P.cov * (exp (t • A))ᵀ)
      (toLp 2 (exp (t • A) *ᵥ ofLp x))) '' P.Z.construct
      = (Real.exp (-(t * A.trace)) • ·) '' ((fun μ => gaussPdf μ P.cov x) '' P.Z.construct) := by
    rw [Set.image_image]
    refine Set.image_congr fun μ _ => ?_
    exact gaussPdf_exp_mulVec A t μ hP x
  dsimp only
  rw [himg, Set.image_smul, Real.sSup_smul_of_nonneg (Real.exp_pos _).le, smul_eq_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

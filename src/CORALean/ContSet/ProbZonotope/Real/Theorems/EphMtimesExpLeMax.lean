module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.EphMtimesExp

@[expose] public section

/-!
# The hull's values over `[0, r]` peak at `t = 0` or `t = r`

`[1, Prop. 3]`'s consequence: "from the monotonicity of `e^{-tr(A)t}` it follows that the PDF
values have a maximum for `t = 0` or `t = r`". For `t ∈ [0, r]` the hull of `e^{At} 𝒵` at
`e^{At} x` is at most the larger of the hull of `𝒵` at `x` and the hull of `e^{Ar} 𝒵` at
`e^{Ar} x`: the factor `e^{-tr(A)t}` is below `1` if `tr(A) ≥ 0` and below its value at `r`
otherwise. The covariance has positive determinant, which makes every density nonnegative.

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

theorem ProbZonotope.eph_mtimes_exp_le_max (P : ProbZonotope n) (hP : 0 < P.cov.det)
    (A : Mat ℝ n n) {r t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    (P.mtimes (exp (t • A))).eph (toLp 2 (exp (t • A) *ᵥ ofLp x))
      ≤ max (P.eph x)
        ((P.mtimes (exp (r • A))).eph (toLp 2 (exp (r • A) *ᵥ ofLp x))) := by -- --- PROOF ---
  -- the hull of `𝒵` is nonnegative
  have hnn : 0 ≤ P.eph x := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨μ, -, rfl⟩
    unfold gaussPdf
    have := Real.rpow_nonneg hP.le (-(1 : ℝ) / 2)
    positivity
  rw [ProbZonotope.eph_mtimes_exp P hP, ProbZonotope.eph_mtimes_exp P hP]
  -- the factor is below `1` or below its value at `r`
  rcases le_total 0 A.trace with h | h
  · refine le_max_of_le_left ?_
    refine mul_le_of_le_one_left hnn ?_
    rw [Real.exp_le_one_iff]
    nlinarith
  · refine le_max_of_le_right ?_
    refine mul_le_mul_of_nonneg_right ?_ hnn
    rw [Real.exp_le_exp]
    nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

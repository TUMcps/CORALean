module

public import CORALean.Global.NormTwoSqEqDotProduct
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-!
# `[1, App. B]`'s rounding is by the dimension of the coefficients, not of the image

The appendix prints `B₂ ⊆ E_q(D⁻¹Uᵀ H) ⊆ n^{1/2-1/q} B₂` for `q ≥ 2`, where the coefficients
`β` of `E_q` live in `ℝᵐ` and the image in `ℝⁿ`. At `n = 1`, `m = 2`, `q = ∞` and
`M = D⁻¹Uᵀ H = (√2/2, √2/2)` (`M Mᵀ = 1`), `M (1, 1) = √2`, a point of `E_∞(M)` outside
`1^{1/2} B₂ = [-1, 1]`; the factor is `m^{1/2} = √2` (`ellipsotope_rounding_of_two_le`).

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp Matrix ENNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem ellipsotope_rounding_counterexample : -- --- STMT ---
    ∃ M : Mat ℝ 1 2, M * Mᵀ = 1 ∧
      ¬ {y : Fin 1 → ℝ | ∃ β : Fin 2 → ℝ, ‖toLp ⊤ β‖ ≤ 1 ∧ y = M *ᵥ β}
        ⊆ {y | ‖toLp 2 y‖
          ≤ ((1 : ℕ) : ℝ) ^ ((2 : ℝ≥0∞)⁻¹ - (⊤ : ℝ≥0∞)⁻¹).toReal} := by -- --- PROOF ---
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the matrix has orthonormal rows
  refine ⟨!![Real.sqrt 2 / 2, Real.sqrt 2 / 2], ?_, fun hsub => ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [mul_apply, Fin.sum_univ_two]
    nlinarith
  · -- the corner `(1, 1)` maps to `√2 > 1`
    have hβ : ‖toLp ⊤ (![1, 1] : Fin 2 → ℝ)‖ ≤ 1 := by
      simpa using (pi_norm_le_iff_of_nonneg zero_le_one (x := (![1, 1] : Fin 2 → ℝ))).mpr
        fun i => by fin_cases i <;> simp
    have := hsub ⟨![1, 1], hβ, rfl⟩
    simp only [Set.mem_setOf_eq, Nat.cast_one, Real.one_rpow] at this
    have hnorm : ‖toLp 2 (!![Real.sqrt 2 / 2, Real.sqrt 2 / 2] *ᵥ (![1, 1] : Fin 2 → ℝ))‖ ^ 2
        = 2 := by
      rw [norm_two_sq_eq_dotProduct]
      simp [mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [norm_nonneg (toLp 2 (!![Real.sqrt 2 / 2, Real.sqrt 2 / 2] *ᵥ (![1, 1] : Fin 2 → ℝ)))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

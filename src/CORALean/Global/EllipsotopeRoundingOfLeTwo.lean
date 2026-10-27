module

public import CORALean.Global.LpNormLeLpNorm
public import CORALean.Global.LpNormLeCardRpowMul
public import CORALean.Global.NormTwoTransposeMulVecEq
public import CORALean.Global.NormTwoMulVecLe

@[expose] public section

/-!
# Rounding an ellipsotope by the Euclidean ball, `q ≤ 2`

`[1, App. B]`: for `M` with orthonormal rows (`M Mᵀ = I`) and `1 ≤ q ≤ 2`,
`B₂ ⊆ m^{1/q-1/2} E_q(M) ⊆ m^{1/q-1/2} B₂`, `E_q(M) = {M β | ‖β‖_q ≤ 1}`, with the dimension `m`
of the coefficient space where the paper prints `n`. A point `y` of `B₂` is
`m^{1/q-1/2} M (m^{1/2-1/q} Mᵀ y)` with `‖Mᵀ y‖_q ≤ m^{1/q-1/2} ‖Mᵀ y‖₂`, and
`‖M β‖₂ ≤ ‖β‖₂ ≤ ‖β‖_q`.

## Inputs
* `q` – exponent of the coefficient norm
* `M` – matrix with orthonormal rows

## Hypotheses
* `hq` – the exponent is at most two
* `hq1` – the exponent is finite
* `hM` – the rows are orthonormal

## Conclusion
* the ellipsotope lies between the Euclidean ball and its dimension-scaled version

## References

* [1] [A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC),
      2024.](../../../references/2024/kulmburg-ecc-zonotope-ellipsotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp Matrix ENNReal

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ellipsotope_rounding_of_le_two {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≤ 2) (hq1 : q ≠ ∞)
    (M : Mat ℝ n m) (hM : M * Mᵀ = 1) : -- --- CONCL ---
    {y : Fin n → ℝ | ‖toLp 2 y‖ ≤ 1}
        ⊆ {y | ∃ β : Fin m → ℝ, ‖toLp q β‖ ≤ 1 ∧ y = (m : ℝ) ^ (q⁻¹ - 2⁻¹).toReal • (M *ᵥ β)} ∧
      {y | ∃ β : Fin m → ℝ, ‖toLp q β‖ ≤ 1 ∧ y = M *ᵥ β}
        ⊆ {y | ‖toLp 2 y‖ ≤ 1} := by -- --- PROOF ---
  refine ⟨fun y hy => ?_, ?_⟩
  -- `Mᵀ y` is in the `ℓ_q` ball once divided by the factor
  · set κ : ℝ := (m : ℝ) ^ (q⁻¹ - 2⁻¹).toReal with hκ
    have hy2 : ‖toLp 2 (Mᵀ *ᵥ y)‖ ≤ 1 := (norm_two_transpose_mulVec_eq M hM y).trans_le hy
    rcases (Real.rpow_nonneg (Nat.cast_nonneg m) _ : 0 ≤ κ).eq_or_lt with h0 | hpos
    · -- `κ = 0` only in dimension `m = 0`, where every vector is `0`
      have hm0 : (m : ℝ) = 0 := ((Real.rpow_eq_zero_iff_of_nonneg (Nat.cast_nonneg m)).mp
        h0.symm).1
      have hm : m = 0 := by exact_mod_cast hm0
      subst hm
      have hz : Mᵀ *ᵥ y = 0 := funext fun i => i.elim0
      have hy0 : ‖toLp 2 y‖ = 0 := by
        rw [← norm_two_transpose_mulVec_eq M hM y, hz]; simp
      have : y = 0 := by simpa using hy0
      exact ⟨0, by rw [toLp_zero, norm_zero]; exact zero_le_one, by simp [this]⟩
    · refine ⟨κ⁻¹ • (Mᵀ *ᵥ y), ?_, ?_⟩
      -- the divided point has `ℓ_q` norm at most `‖Mᵀ y‖₂`
      · rw [toLp_smul, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
        have h2 := lpNorm_le_card_rpow_mul (p := q) (q := 2) hq hq1 (Mᵀ *ᵥ y)
        rw [← hκ] at h2
        calc κ⁻¹ * ‖toLp q (Mᵀ *ᵥ y)‖ ≤ κ⁻¹ * (κ * ‖toLp 2 (Mᵀ *ᵥ y)‖) :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hpos.le)
          _ = ‖toLp 2 (Mᵀ *ᵥ y)‖ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
          _ ≤ 1 := hy2
      · rw [mulVec_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, mulVec_mulVec, hM,
          one_mulVec]
  · rintro _ ⟨β, hβ, rfl⟩
    exact (norm_two_mulVec_le M hM β).trans ((lpNorm_le_lpNorm hq hq1 β).trans hβ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Taylm.Float.Operations.BernsteinStep
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# A Bernstein step lies in its bracket

For `j ≤ N`, the term `C(j, i) / C(N, i) · (C(e, i) 2ⁱ (-1)^(e - i))` of `bernsteinEntry` lies
between the two floats `bernsteinStep` returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bernsteinStep_mem (N e j i : ℕ) (hj : j ≤ N) :
    toReal (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).1
        ≤ ((j.choose i : ℝ) / (N.choose i : ℝ)) * ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i)) ∧
      ((j.choose i : ℝ) / (N.choose i : ℝ)) * ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i))
        ≤ toReal (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).2 := by -- --- PROOF ---
  unfold Taylm.bernsteinStep
  by_cases hij : i ≤ j
  · simp only [if_pos hij]
    have hiN : i ≤ N := le_trans hij hj
    have hcN : (1 : ℝ) ≤ (N.choose i : ℝ) := by exact_mod_cast Nat.choose_pos hiN
    have hcj : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have hle : (j.choose i : ℝ) ≤ (N.choose i : ℝ) := by exact_mod_cast Nat.choose_le_choose i hj
    have hNd := intDown_le_intUp (𝕋 := 𝕋) (N.choose i : ℤ)
    have hjd := intDown_le_intUp (𝕋 := 𝕋) (j.choose i : ℤ)
    simp only [Int.cast_natCast] at hNd hjd
    have hup : (0 : ℝ) < toReal (intUp (N.choose i : ℤ) : 𝕋) := lt_of_lt_of_le (by linarith) hNd.2
    -- the ratio from below
    have hrLo : toReal (divDown (intDown (j.choose i : ℤ)) (intUp (N.choose i : ℤ)) : 𝕋)
        ≤ (j.choose i : ℝ) / (N.choose i : ℝ) := by
      refine le_trans (divDown_le_div _ _ hup) ?_
      by_cases hneg : toReal (intDown (j.choose i : ℤ) : 𝕋) < 0
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg.le hup.le)
          (div_nonneg hcj (by linarith))
      · replace hneg := not_lt.mp hneg
        exact div_le_div₀ hcj hjd.1 (by linarith) hNd.2
    -- the ratio from above
    have hrHi : (j.choose i : ℝ) / (N.choose i : ℝ) ≤ toReal
        (if le (one : 𝕋) (intDown (N.choose i : ℤ)) then
          divUp (intUp (j.choose i : ℤ)) (intDown (N.choose i : ℤ)) else (one : 𝕋)) := by
      split_ifs with hb
      · have hb1 := toReal_le_of_le hb
        rw [toReal_one] at hb1
        refine le_trans ?_ (div_le_divUp _ _ (by linarith))
        exact div_le_div₀ (le_trans hcj hjd.2) hjd.2 (by linarith) hNd.1
      · rw [toReal_one]
        exact (div_le_one (by linarith)).2 hle
    -- the signed integer
    have hc := intDown_le_intUp (𝕋 := 𝕋) ((e.choose i : ℤ) * 2 ^ i * (-1) ^ (e - i))
    push_cast at hc
    have hP := Real.Interval.mul_between_corners hrLo hrHi hc.1 hc.2
    exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hP.1, le_trans hP.2 (Interval.le_mulHi _ _ _ _)⟩
  · simp only [if_neg hij]
    have h0 : j.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

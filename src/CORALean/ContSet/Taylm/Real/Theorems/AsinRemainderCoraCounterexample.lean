module

public import CORALean.ContSet.Taylm.Real.Operations.AsinPolyCora
public import CORALean.ContSet.Taylm.Real.Operations.AsinRemainderUpperCora
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# CORA's `asin(taylm)` remainder is too small

For `taylm(interval(-1, 1), 7)` the polynomial is `x + x³/6 + 3x⁵/40 + 5x⁷/112` and the remainder
interval `[0, (π/2)⁸/8!] ≈ [0, 0.00092]` (the unit test `test_taylm_asin` asserts it). At
`x = 1` the model is therefore `[1.2863, 1.2872]`, while `asin 1 = π/2 ≈ 1.5708`: the true error
of the polynomial is `0.2845`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polynomial at `x = 1`, order `7`. -/
theorem Taylm.aux_asinPoly_seven_one :
    Taylm.asinPolyCora 7 1 = 1 + 1 / 6 + 3 / 40 + 5 / 112 := by
  simp [Taylm.asinPolyCora, Finset.sum_range_succ, Taylm.asinFactor1Cora,
    Taylm.asinDasinCora, Nat.factorial]
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `x = 1` CORA's enclosure `[p(1), p(1) + R]` misses `asin 1`: its upper end is below. -/
theorem Taylm.asin_remainder_cora_counterexample :
    Taylm.asinPolyCora 7 1 + Taylm.asinRemainderUpperCora 7 1 < Real.arcsin 1 := by -- --- PROOF ---
  rw [Taylm.aux_asinPoly_seven_one, Taylm.asinRemainderUpperCora, Real.arcsin_one]
  -- `3.14 < π < 3.15`
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have hp : 0 < Real.pi / 2 := by linarith
  have h3 : (Real.pi / 2) ^ 8 ≤ (1.575 : ℝ) ^ 8 :=
    pow_le_pow_left₀ hp.le (by linarith) 8
  norm_num [Nat.factorial] at h3 ⊢
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

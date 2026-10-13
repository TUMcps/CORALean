import CORALean.ContSet.Taylm.Real.Operations.Smul
import CORALean.ContSet.Taylm.Real.Definitions.Scaled
import CORALean.ContSet.Interval.Real.Theorems.AbsMulLoMulHiLe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Taylm.smul` keeps the scaling

A scalar multiple of a model scaled by `C` is scaled by `|a|·C`: every coefficient and both
remainder ends are multiplied by `a`. A step of [1, Thm. 1]'s intrinsics, which are linear
combinations of powers.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.smul_scaled {T : Taylm n} {h C : ℝ} (a : ℝ) (hT : T.Scaled h C) :
    (T.smul a).Scaled h (|a| * C) := by -- --- PROOF ---
  obtain ⟨w, i, s⟩ := hT
  have m := Interval.abs_mulLo_mulHi_le (le_refl |a|) (le_refl |a|) i s
  refine ⟨?_, by simpa [Taylm.smul, mul_assoc] using m.1,
    by simpa [Taylm.smul, mul_assoc] using m.2⟩
  -- the weight scales by `|a|`
  have : Taylm.weight (T.smul a).terms h = |a| * Taylm.weight T.terms h := by
    simp only [Taylm.smul, Taylm.weight, List.map_map, ← List.sum_map_mul_left]
    refine congrArg (List.sum (α := ℝ)) (List.map_congr_left fun b _ => ?_)
    simp [abs_mul, mul_div_assoc]
  rw [this]
  exact mul_le_mul_of_nonneg_left w (abs_nonneg a)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

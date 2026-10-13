import CORALean.ContSet.Capsule.Real.Operations.OfPoint
import CORALean.ContSet.Capsule.Real.Theorems.OfPointMem
import Mathlib.Analysis.Normed.Field.Basic

/-!
# `Capsule.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: a radius of `0` pins the squared distance to the
segment to `0`, and the segment of direction `0` is the point itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.mem_ofPoint_iff (v x : Vec ℝ n) :
    x ∈ (Capsule.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨t, -, h⟩
    simp only [Capsule.ofPoint] at h
    have h0 : ∑ i, (x i - v i) ^ 2 = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp
        (le_antisymm (by simpa using h) (Real.sqrt_nonneg _)))
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i - v i)).mp h0 i
      (Finset.mem_univ i)
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  · rintro rfl
    exact Capsule.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

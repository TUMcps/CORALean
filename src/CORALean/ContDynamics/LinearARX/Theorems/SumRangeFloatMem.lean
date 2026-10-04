import CORALean.ContDynamics.LinearARX.Operations.SumRangeFloat
import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The interval sum holds the real sum

If each real matrix `M t` lies in the interval matrix `f t`, then `∑ t ∈ range k, M t` lies in
`sumRangeFloat f k`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.sumRangeFloat_mem (f : ℕ → Interval (Mat 𝕋 m n)) (M : ℕ → Mat ℝ m n)
    (h : ∀ t, M t ∈ (f t).construct) (k : ℕ) :
    ∑ t ∈ Finset.range k, M t ∈ (LinearARX.sumRangeFloat f k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the empty sum is the zero matrix, stored exactly
    have hz : toRealMat (show Mat 𝕋 m n from fun _ _ => zero) = 0 := by
      funext i l
      simp [toRealMat, toReal_zero]
    rw [Finset.sum_range_zero, ← hz]
    exact Interval.mem_point _
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact Interval.matPlus_outer _ _ ih (h k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

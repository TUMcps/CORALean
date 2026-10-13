import CORALean.ContSet.Taylm.Float.Operations.BinomCoef
import CORALean.ContSet.Interval.Float.Theorems.PowLoLe
import CORALean.ContSet.Interval.Float.Theorems.PowHiLe
import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# The binomial coefficient lies in its bracket

The integer, the two powers and their products each lie between their directed roundings, so
`C(e, j) · mᵉ⁻ʲ · rʲ` lies between the two floats `binomCoef` returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.binomCoef_mem (e j : ℕ) (m r : 𝕋) :
    toReal (Taylm.binomCoef e j m r).1 ≤ (e.choose j : ℝ) * toReal m ^ (e - j) * toReal r ^ j ∧
      (e.choose j : ℝ) * toReal m ^ (e - j) * toReal r ^ j ≤
        toReal (Taylm.binomCoef e j m r).2 := by -- --- PROOF ---
  -- the integer between its roundings
  have hI := intDown_le_intUp (𝕋 := 𝕋) (e.choose j : ℤ)
  simp only [Int.cast_natCast] at hI
  -- the first product, with the power of the centre
  have hA := Real.Interval.mul_between_corners hI.1 hI.2 (Interval.powLo_le m (e - j))
    (Interval.le_powHi m (e - j))
  have hA₁ := le_trans (Interval.mulLo_le _ _ _ _) hA.1
  have hA₂ := le_trans hA.2 (Interval.le_mulHi _ _ _ _)
  -- the second, with the power of the radius
  have hB := Real.Interval.mul_between_corners hA₁ hA₂ (Interval.powLo_le r j)
    (Interval.le_powHi r j)
  exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hB.1, le_trans hB.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

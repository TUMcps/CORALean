module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetCoef
public import CORALean.ContSet.Interval.Float.Theorems.PowLoLe
public import CORALean.ContSet.Interval.Float.Theorems.PowHiLe
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# The binomial coefficient lies in its bracket

The integer, the two powers and their products each lie between their directed roundings, so `C(e,
j) · cenᵉ⁻ʲ · radʲ` lies between the two floats `getSubsetCoef` returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.getSubsetCoef_mem (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋)
    (i : Fin pZ.h) (j : ℕ) :
    toReal (pZ.getSubsetCoef k cen rad i j).inf ≤
        ((pZ.E k i).choose j : ℝ) * toReal cen ^ (pZ.E k i - j) * toReal rad ^ j ∧
      ((pZ.E k i).choose j : ℝ) * toReal cen ^ (pZ.E k i - j) * toReal rad ^ j ≤
        toReal (pZ.getSubsetCoef k cen rad i j).sup := by -- --- PROOF ---
  -- the integer between its roundings
  have hI := intDown_le_intUp (𝕋 := 𝕋) ((pZ.E k i).choose j : ℤ)
  simp only [Int.cast_natCast] at hI
  -- the first product, with the power of the centre
  have hA := Real.Interval.mul_between_corners hI.1 hI.2 (Interval.powLo_le cen (pZ.E k i - j))
    (Interval.le_powHi cen (pZ.E k i - j))
  have hA₁ := le_trans (Interval.mulLo_le _ _ _ _) hA.1
  have hA₂ := le_trans hA.2 (Interval.le_mulHi _ _ _ _)
  -- the second, with the power of the radius
  have hB := Real.Interval.mul_between_corners hA₁ hA₂ (Interval.powLo_le rad j)
    (Interval.le_powHi rad j)
  exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hB.1, le_trans hB.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

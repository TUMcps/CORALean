import CORALean.ContSet.Interval.Float.Operations.EvalList
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.Global.EvalList

/-!
# `Interval.evalList` encloses the polynomial

At every point of the box `[lo, hi]` the polynomial's value lies between the two ends.
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

theorem Interval.evalList_mem {lo hi : 𝕋} {x : ℝ} (h₁ : toReal lo ≤ x) (h₂ : x ≤ toReal hi)
    (l : List ℤ) :
    toReal (Interval.evalList lo hi l).1 ≤ evalL l x ∧
      evalL l x ≤ toReal (Interval.evalList lo hi l).2 := by -- --- PROOF ---
  induction l with
  | nil => simp [Interval.evalList, evalL, toReal_zero]
  | cons a l ih =>
    have hm := Interval.mul_between_corners h₁ h₂ ih.1 ih.2
    have ha := intDown_le_intUp (𝕋 := 𝕋) a
    have h3 := addDown_le_add (intDown a : 𝕋) (Interval.mulLo lo hi (Interval.evalList lo hi l).1
      (Interval.evalList lo hi l).2)
    have h4 := add_le_addUp (intUp a : 𝕋) (Interval.mulHi lo hi (Interval.evalList lo hi l).1
      (Interval.evalList lo hi l).2)
    simp only [Interval.evalList, evalL]
    constructor <;> linarith [ha.1, ha.2, hm.1, hm.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

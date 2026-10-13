import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The reach of a point from the centre, below its rounded bound

A real `x` between `lo` and `hi` is within `max 0 (max (hi ⊖ c) (c ⊖ lo))`, rounded up, of
the centre `c`: the radius every Taylor remainder bound of `Taylm` starts from.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x ∈ [lo, hi]` is within the rounded-up reach of the hull from `c`. -/
theorem abs_sub_le_maximum_subUp {x : ℝ} {lo hi : 𝕋} (c : 𝕋) (hlo : toReal lo ≤ x)
    (hhi : x ≤ toReal hi) :
    |x - toReal c|
      ≤ toReal (maximum zero (maximum (subUp hi c) (subUp c lo))) := by -- --- PROOF ---
  have h1 := sub_le_subUp hi c
  have h2 := sub_le_subUp c lo
  simp only [toReal_maximum, toReal_zero]
  rw [abs_le]
  constructor
  · linarith [le_max_right (0 : ℝ) (max (toReal (subUp hi c)) (toReal (subUp c lo))),
      le_max_right (toReal (subUp hi c)) (toReal (subUp c lo))]
  · linarith [le_max_right (0 : ℝ) (max (toReal (subUp hi c)) (toReal (subUp c lo))),
      le_max_left (toReal (subUp hi c)) (toReal (subUp c lo))]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

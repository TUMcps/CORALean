module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap

@[expose] public section

/-!
# A directed sum of per-term minima never overshoots a bilinear value

`Q *ᵥ Gⱼ` is known to an interval, and which endpoint of `Gᵢ(r) · [lo, hi]` is
the lower depends on the sign of `Gᵢ(r)`; taking both and picking with `min` is
how the layer avoids ever asking.

## Inputs
* `g` – vector
* `wlo` – lower bound of the second vector
* `whi` – upper bound of the second vector
* `w` – point between the bounds

## Hypotheses
* `hw` – point lies between the bounds

## Conclusion
* the rounded-down bound is at most the exact dot product
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_min_mul_le {a lo hi w : ℝ} (h1 : lo ≤ w) (h2 : w ≤ hi) :
    min (a * lo) (a * hi) ≤ a * w := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 ha)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 ha)


-- =======================================  MAIN THEOREM  ======================================= --

-- so a directed sum of per-term extremes brackets the exact bilinear value
theorem PolyZonotope.quadDown_le {g wlo whi : Vec 𝕋 n} {w : Vec ℝ n}
    (hw : ∀ r, toReal (wlo r) ≤ w r ∧ w r ≤ toReal (whi r)) :
    toReal (PolyZonotope.quadDown g wlo whi) ≤ ∑ r, toReal (g r) * w r := by
  refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun r _ => ?_)
  rw [toReal_minimum]
  exact le_trans (min_le_min (mulDown_le_mul _ _) (mulDown_le_mul _ _))
    (PolyZonotope.aux_min_mul_le (hw r).1 (hw r).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

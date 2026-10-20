module

public import CORALean.ContSet.Zonotope.Float.Operations.EntryDeviation
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `entryDeviation` bounds `|x - e - y|`

The first difference rounded upward is above `x - e - y` because `lo ≤ y`, the second above
`y - (x - e)` because `y ≤ hi`, so the larger is above the magnitude.

## Inputs
* `x` – point
* `e` – box corner
* `lo` – lower bound of the entry
* `hi` – upper bound of the entry
* `y` – value between the bounds
* `i` – entry

## Hypotheses
* `hlo` – lower bound holds
* `hhi` – upper bound holds

## Conclusion
* deviation is bounded by the computed bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.entryDeviation_bound (x e lo hi : Vec 𝕋 n) {y : ℝ} (i : Fin n)
    (hlo : toReal (lo i) ≤ y) (hhi : y ≤ toReal (hi i)) : -- --- CONCL ---
    |toReal (x i) - toReal (e i) - y|
      ≤ toReal (Zonotope.entryDeviation x e lo hi i) := by -- --- PROOF ---
  have a1 := sub_le_subUp (x i) (e i)
  have a2 := sub_le_subUp (subUp (x i) (e i)) (lo i)
  have b1 := subDown_le_sub (x i) (e i)
  have b2 := sub_le_subUp (hi i) (subDown (x i) (e i))
  simp only [Zonotope.entryDeviation, toReal_maximum]
  have m1 := le_max_left (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  have m2 := le_max_right (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

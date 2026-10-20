module

public import CORALean.ContSet.Zonotope.Float.Operations.Deviation
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `deviation` bounds every entry of `|x - e - y|`

The first difference rounded upward is above `x - e - y` because `lo ≤ y`, the second above
`y - (x - e)` because `y ≤ hi`, so the larger is above the magnitude; `maximumOver` is above each
entry.

## Inputs
* `x` – point
* `e` – box corner
* `lo` – lower bound of the vector
* `hi` – upper bound of the vector
* `y` – vector between the bounds
* `i` – entry

## Hypotheses
* `hlo` – lower bound holds
* `hhi` – upper bound holds

## Conclusion
* entry of the deviation is bounded by the computed bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.deviation_bound (x e lo hi : Vec 𝕋 n) (y : Vec ℝ n)
    (hlo : ∀ i, toReal (lo i) ≤ y i) (hhi : ∀ i, y i ≤ toReal (hi i)) (i : Fin n) :
    |toReal (x i) - toReal (e i) - y i|
      ≤ toReal (Zonotope.deviation x e lo hi) := by -- --- PROOF ---
  refine le_trans ?_ (le_maximumOver _ i)
  have a1 := sub_le_subUp (x i) (e i)
  have a2 := sub_le_subUp (subUp (x i) (e i)) (lo i)
  have b1 := subDown_le_sub (x i) (e i)
  have b2 := sub_le_subUp (hi i) (subDown (x i) (e i))
  rw [toReal_maximum]
  have h1 := hlo i
  have h2 := hhi i
  have m1 := le_max_left (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  have m2 := le_max_right (toReal (subUp (subUp (x i) (e i)) (lo i)))
    (toReal (subUp (hi i) (subDown (x i) (e i))))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

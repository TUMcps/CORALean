import CORALean.ContSet.ConPolyZono.Float.Operations.Split
import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover

/-!
# The halves of `ConPolyZono.split` cover the set, over a floating-point scalar

Each half contains the set intersected with a box (`intersection_outer`), and the set lies in
its bounding box, which the two half boxes cover (`splitAt_cover`). Outer, not exact: the
float `intersection` is an enclosure.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.split_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    cPZ.construct ⊆ (cPZ.split d).1.construct ∪ (cPZ.split d).2.construct := by -- --- PROOF ---
  intro x hx
  -- the set is in its box, which the two half boxes cover
  rcases cPZ.interval.splitAt_cover d (cPZ.interval_contains hx) with h | h
  · exact Or.inl (ConPolyZono.intersection_outer _ _ ⟨hx, Interval.conPolyZono_contains _ h⟩)
  · exact Or.inr (ConPolyZono.intersection_outer _ _ ⟨hx, Interval.conPolyZono_contains _ h⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

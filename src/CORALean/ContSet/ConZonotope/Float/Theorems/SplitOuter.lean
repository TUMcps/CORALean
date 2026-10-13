import CORALean.ContSet.ConZonotope.Float.Operations.Split
import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover

/-!
# The halves of `ConZonotope.split` cover the set, over a floating-point scalar

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

theorem ConZonotope.split_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    cZ.construct ⊆ (cZ.split d).1.construct ∪ (cZ.split d).2.construct := by -- --- PROOF ---
  intro x hx
  -- the set is in its box, which the two half boxes cover
  rcases cZ.interval.splitAt_cover d (cZ.interval_contains hx) with h | h
  · exact Or.inl (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)
  · exact Or.inr (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

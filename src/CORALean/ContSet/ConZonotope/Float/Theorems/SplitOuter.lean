module

public import CORALean.ContSet.ConZonotope.Float.Operations.Split
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The halves of `ConZonotope.split` cover the set, over a floating-point scalar

Each half contains the set intersected with a box (`intersection_outer`), and the set lies in
its bounding box, which the two half boxes cover (`splitAt_cover`). Outer, not exact: the
float `intersection` is an enclosure.

## Inputs
* `cZ` – float constrained zonotope
* `d` – dimension to cut along

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.split_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (d : Fin n) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.split d).fst.construct ∪ (cZ.split d).snd.construct := by -- --- PROOF ---
  intro x hx
  -- the set is in its box, which the two half boxes cover
  rcases cZ.interval.splitAt_cover d (cZ.interval_contains hx) with h | h
  · exact Or.inl (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)
  · exact Or.inr (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

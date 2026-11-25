module

public import CORALean.ContSet.ConZonotope.Float.Operations.SplitWith
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
# The halves of `ConZonotope.splitWith` cover the set, over a floating-point scalar

Each half contains the set intersected with a half of the box (`intersection_outer`), and the
set lies in the box, which the two halves cover (`splitAt_cover`). Outer, not exact: the float
`intersection` is an enclosure.

## Inputs
* `cZ` – float constrained zonotope
* `I` – box
* `d` – dimension to cut along

## Hypotheses
* `hI` – the set lies in the box

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.splitWith_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {I : Interval (Vec 𝕋 n)}
    (hI : cZ.toSet ⊆ I.toSet) (d : Fin n) : -- --- CONCL ---
    cZ.toSet ⊆ (cZ.splitWith I d).fst.toSet ∪ (cZ.splitWith I d).snd.toSet := by -- --- PROOF ---
  intro x hx
  -- the set is in the box, which the two half boxes cover
  rcases I.splitAt_cover d (hI hx) with h | h
  · exact Or.inl (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)
  · exact Or.inr (ConZonotope.intersection_outer _ _ ⟨hx, Interval.conZonotope_contains _ h⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

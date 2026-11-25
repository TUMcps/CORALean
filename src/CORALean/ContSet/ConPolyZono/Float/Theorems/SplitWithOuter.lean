module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitWith
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# The halves of `ConPolyZono.splitWith` cover the set, over a floating-point scalar

Each half contains the set intersected with a half of the box (`intersection_outer`), the half
lying in its zonotope and that in its constrained polynomial zonotope; the set lies in the box,
which the two halves cover (`splitAt_cover`). Outer, not exact: the float `intersection` is an
enclosure.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `I` – box
* `d` – coordinate to split along

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

theorem ConPolyZono.splitWith_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {I : Interval (Vec 𝕋 n)}
    (hI : cPZ.toSet ⊆ I.toSet) (d : Fin n) : -- --- CONCL ---
    cPZ.toSet ⊆ (cPZ.splitWith I d).fst.toSet ∪ (cPZ.splitWith I d).snd.toSet := by -- --- PROOF ---
  intro x hx
  -- the set is in the box, which the two half boxes cover; each half is in its conversion
  rcases I.splitAt_cover d (hI hx) with h | h
  · exact Or.inl (ConPolyZono.intersection_outer _ _
      ⟨hx, Zonotope.conPolyZono_contains _ (Interval.zonotope_contains _ h)⟩)
  · exact Or.inr (ConPolyZono.intersection_outer _ _
      ⟨hx, Zonotope.conPolyZono_contains _ (Interval.zonotope_contains _ h)⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConZonotope.Float.Operations.Split
public import CORALean.ContSet.ConZonotope.Float.Theorems.SplitWithOuter
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

The set lies in its bounding box, and `split` is `splitWith` at that box, whose halves cover
every set in the box (`splitWith_outer`). Outer, not exact: the float `intersection` is an
enclosure.

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

theorem ConZonotope.split_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    cZ.toSet ⊆ (cZ.split d).fst.toSet ∪ (cZ.split d).snd.toSet := by
  -- the set lies in its bounding box, at which `split` is `splitWith`
  exact cZ.splitWith_outer (fun _ hx => cZ.interval_contains hx) d

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.ConZonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains

@[expose] public section

/-!
# `ConZonotope.reduce` over-approximates

Above the order it is the zonotope's `reduce` composed with forgetting the
constraints, both enclosures; at or below it, the identity.

## Inputs
* `cZ` – float constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (o : ℕ) : -- --- CONCL ---
    cZ.construct ⊆ (cZ.reduce o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduce
  split_ifs with hlt
  · exact subset_trans (subset_trans (ConZonotope.zonotope_contains cZ)
      (Zonotope.reduce_outer cZ.zonotope o)) (Zonotope.conZonotope_contains _)
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

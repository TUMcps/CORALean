module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# `reduceGirard` over-approximates the set

Sound at every pair of partitions, as over ℝ, so a selection rule owes no
proof — `reduceGirard_outer` is `reduceBy_outer` at Girard's own partition.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirard_outer (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer pZ _ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# Girard's reduction encloses

Two cases: below the order there is nothing to do, and above it the rule is a
pair of partitions like any other. The metric never appears, which is what lets
`sortPerm`'s unconstrained comparator rank a float.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) :
    cPZ.construct ⊆ (cPZ.reduceGirard o).construct := by
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact ConPolyZono.reduceBy_outer cPZ _ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

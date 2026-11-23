module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactCora
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FoldConstantsOuter

@[expose] public section

/-!
# `PolyZonotope.compactCora` over-approximates

Folding the constants, dropping the unused factors and the constructor each keep the set inside
(`foldConstants_outer`, `compactFactors_outer`, `construct_outer`).

## Inputs
* `order` – the order of the columns
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactCora_outer (order : ℕ → Array (Array ℕ) → Array ℕ)
    (pZ : PolyZonotope (Vec 𝕋 n)) : pZ.toSet ⊆ (pZ.compactCora order).toSet :=
  subset_trans (PolyZonotope.foldConstants_outer pZ)
    (subset_trans (PolyZonotope.compactFactors_outer _) (PolyZonotope.construct_outer _ order))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

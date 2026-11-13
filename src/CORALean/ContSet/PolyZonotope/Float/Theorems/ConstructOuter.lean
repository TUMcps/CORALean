module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PickOuter

@[expose] public section

/-!
# CORA's constructor encloses

The three steps each enclose: `pick` of the nonzero generators, `compactGens`, `pick` of the
order.

## Inputs
* `pZ` – polynomial zonotope
* `order` – the order of the merged classes

## Hypotheses
* none

## Conclusion
* the set is contained in the constructed one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.construct_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (order : ℕ → Array (Array ℕ) → Array ℕ) : pZ.toSet ⊆ (pZ.construct order).toSet :=
  subset_trans (PolyZonotope.pick_outer _ _ _)
    (subset_trans (PolyZonotope.compactGens_outer _) (PolyZonotope.pick_outer _ _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

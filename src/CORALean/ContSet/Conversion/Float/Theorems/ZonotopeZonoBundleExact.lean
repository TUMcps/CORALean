module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ToSetEqIInter
public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Conversion.Float.Operations.Basic

@[expose] public section

/-!
# A zonotope as a bundle of one, over a floating-point scalar

Exact: the float bundle denotes the intersection of its members' own inflated
sets, so a one-member family denotes that member and nothing else
(`Set.iInter_const` at `Fin 1`). The member keeps its own error box.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope equals its zonotope bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonoBundle_exact (Z : Zonotope (Vec 𝕋 n)) :
    Z.toSet = Z.zonoBundle.toSet := by
  rw [ZonoBundle.toSet_eq_iInter]
  show Z.toSet = ⋂ _ : Fin 1, Z.toSet
  exact (Set.iInter_const Z.toSet).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

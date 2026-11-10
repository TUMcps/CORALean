module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ToSetEqIInter
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A zonotope is a bundle of one

Exact: a single-zonotope family intersects nothing but itself, so the
intersection it denotes is the zonotope's own set, `Set.iInter_const` at the
one-element index type `Fin 1`.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope equals its zonotope bundle
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonoBundle_exact (Z : Zonotope α) :
    Z.toSet = Z.zonoBundle.toSet := by
  rw [ZonoBundle.toSet_eq_iInter]
  show Z.toSet = ⋂ _ : Fin 1, Z.toSet
  exact (Set.iInter_const Z.toSet).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

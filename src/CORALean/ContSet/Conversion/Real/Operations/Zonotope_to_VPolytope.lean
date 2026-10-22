module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.Corners
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A zonotope as its corners

## Inputs
* `Z` – zonotope
* `σ` – sign per generator

## Output
* vertex picked out by the signs
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertex a choice of sign per generator picks out. -/
def Zonotope.corner (Z : Zonotope α) (σ : Fin Z.h → Bool) : α :=
  Z.c + ∑ j, (if σ j then (1:ℝ) else -1) • Z.G j

/-- The hull of a zonotope's `2^h` corners, one per sign pattern of its coefficients. -/
noncomputable def Zonotope.vPolytope (Z : Zonotope α) : VPolytope α where
  k := 2 ^ Z.h
  V := fun l => Z.corner (signEquiv Z.h l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

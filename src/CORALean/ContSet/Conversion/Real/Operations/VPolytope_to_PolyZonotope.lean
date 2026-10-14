module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import Mathlib.Analysis.Convex.Join

@[expose] public section

/-!
# A hull as a polynomial zonotope — the construction

`VPolytope.polyZonotope` is the construction; `VPolytope_to_PolyZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.polyZonotope (P : VPolytope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  P.zonotope.polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.Corners
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A zonotope as its corners

`Zonotope.contains_vPolytope`: it contains its `vPolytope`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- back: each listed vertex is a corner, and every corner lies in the zonotope
theorem Zonotope.contains_vPolytope (Z : Zonotope α) :
    Z.vPolytope.construct ⊆ Z.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ Z.convex_construct
  rintro _ ⟨l, rfl⟩
  exact ⟨fun j => if signEquiv Z.h l j then (1 : ℝ) else -1,
    fun j => by dsimp only; split_ifs <;> norm_num, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Theorems.UnderapproximateMem
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `underapproximate` is an inner approximation

The points, and their convex hull, lie inside the zonotope: a subset, not a superset.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inner, as a set: the convex hull of the returned vertices is a subset of the zonotope. -/
theorem Zonotope.underapproximate_convexHull_subset {n k : ℕ} (Z : Zonotope (Vec ℝ n))
    (S : Fin k → Vec ℝ n) :
    convexHull ℝ (Set.range fun p : Fin k × Bool => Z.underapproximate S p.1 p.2) ⊆
      Z.construct :=
  convexHull_min (by rintro _ ⟨p, rfl⟩; exact Zonotope.underapproximate_mem Z S p.1 p.2)
    Z.convex_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

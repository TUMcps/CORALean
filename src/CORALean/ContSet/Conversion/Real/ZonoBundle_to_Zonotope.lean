import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# One component of a bundle, enclosing it

CORA's cheapest route out of a `zonoBundle`: any single component already
encloses the whole intersection. The choice of `i` owes no proof, since the
guarantee below is sound at every one — `ConPolyZono.reduceBy_outer` is the
same shape, sound at every partition.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ZonoBundle.zonotope (zB : ZonoBundle α) (i : Fin zB.k) : Zonotope α := zB.Z i


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.zonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.zonotope i).construct :=
  Set.iInter_subset _ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

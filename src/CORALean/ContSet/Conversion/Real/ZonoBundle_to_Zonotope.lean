module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_Zonotope

@[expose] public section

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.zonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.zonotope i).construct :=
  Set.iInter_subset _ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

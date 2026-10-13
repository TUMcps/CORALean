module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A polynomial zonotope as a constrained zonotope

Through the zonotope enclosure, then the constrained zonotope with nothing to
satisfy — that second leg is exact, so all the loss is the polynomial
zonotope's own zonotope step. A polynomial zonotope's set is generally not even
convex, so no constrained zonotope is exact for it: a direct construction would
be tighter.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.conZonotope (pZ : PolyZonotope α) : ConZonotope α :=
  pZ.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.conZonotope_contains (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.conZonotope.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.conZonotope_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

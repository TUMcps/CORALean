module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A constrained polynomial zonotope as a bundle of one

Through `ConPolyZono.zonotope`, which drops the constraints and then the
sharing, then `Zonotope.zonoBundle` — the single-member bundle, exact by
`Set.iInter_const`. All the loss is the first leg's, so this is no worse than
`ConPolyZono → Zonotope` already is.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.zonoBundle (cPZ : ConPolyZono α) : ZonoBundle α :=
  cPZ.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.zonoBundle_contains (cPZ : ConPolyZono α) :
    cPZ.construct ⊆ cPZ.zonoBundle.construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

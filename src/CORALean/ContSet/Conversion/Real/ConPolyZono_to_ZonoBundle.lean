import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A constrained polynomial zonotope as a bundle of one

Through `ConPolyZono.zonotope`, which drops the constraints and then the
sharing, then `Zonotope.zonoBundle` — the single-member bundle, exact by
`Set.iInter_const`. All the loss is the first leg's, so this is no worse than
`ConPolyZono → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.zonoBundle (C : ConPolyZono α) : ZonoBundle α :=
  C.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.subset_zonoBundle (C : ConPolyZono α) :
    C.construct ⊆ C.zonoBundle.construct :=
  subset_trans C.zonotope_outer (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

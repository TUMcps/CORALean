import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A constrained zonotope as a bundle of one

Through `ConZonotope.zonotope`, which drops the constraints, then
`Zonotope.zonoBundle` — the single-member bundle, exact by `Set.iInter_const`.
All the loss is the first leg's, so this is no worse than
`ConZonotope → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.zonoBundle (C : ConZonotope α) : ZonoBundle α :=
  C.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.subset_zonoBundle (C : ConZonotope α) :
    C.construct ⊆ C.zonoBundle.construct :=
  subset_trans C.zonotope_outer (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

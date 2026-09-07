import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A polynomial zonotope as a bundle of one

Through `PolyZonotope.zonotope`, which reads every dependent generator as an
independent one, then `Zonotope.zonoBundle` — the single-member bundle, exact by
`Set.iInter_const`. All the loss is the first leg's, so this is no worse than
`PolyZonotope → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.zonoBundle (pZ : PolyZonotope α) : ZonoBundle α :=
  pZ.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subset_zonoBundle (pZ : PolyZonotope α) :
    pZ.construct ⊆ pZ.zonoBundle.construct :=
  subset_trans pZ.zonotope_outer (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

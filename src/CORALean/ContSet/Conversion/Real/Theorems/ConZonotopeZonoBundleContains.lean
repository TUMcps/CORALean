module

public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A constrained zonotope as a bundle of one

Through `ConZonotope.zonotope`, which drops the constraints, then
`Zonotope.zonoBundle` — the single-member bundle, exact by `Set.iInter_const`.
All the loss is the first leg's, so this is no worse than
`ConZonotope → Zonotope` already is.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zonoBundle_contains (cZ : ConZonotope α) :
    cZ.construct ⊆ cZ.zonoBundle.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

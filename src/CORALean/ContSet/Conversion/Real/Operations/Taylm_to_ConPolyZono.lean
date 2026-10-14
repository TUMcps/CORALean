module

public import CORALean.ContSet.Conversion.Real.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# An array of Taylor models as a constrained polynomial zonotope — the construction

`Taylm.conPolyZono` is the construction; `Taylm_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.conPolyZono (T : Fin m → Taylm n) : ConPolyZono (Vec ℝ m) :=
  (Taylm.polyZonotope T).conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# An array of Taylor models as a constrained polynomial zonotope

CORA's `conPolyZono(taylm)`, which goes through `polyZonotope` and adds no constraint;
exact where that is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}

noncomputable def Taylm.conPolyZono (T : Fin m → Taylm n) : ConPolyZono (Vec ℝ m) :=
  (Taylm.polyZonotope T).conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.conPolyZono_exact (T : Fin m → Taylm n) (hT : ∀ i, (T i).remInf ≤ (T i).remSup) :
    (Taylm.conPolyZono T).construct = Taylm.construct T :=
  ((Taylm.polyZonotope T).conPolyZono_exact).symm.trans (Taylm.polyZonotope_exact T hT)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

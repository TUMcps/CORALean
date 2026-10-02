import CORALean.ContSet.Conversion.Real.Taylm_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

/-!
# An array of Taylor models as a constrained polynomial zonotope

CORA's `conPolyZono(taylm)`, which goes through `polyZonotope` and adds no constraint;
exact where that is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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

import CORALean.ContSet.Taylm.Real.Operations.RepresentsaPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.RepresentsaPointConstruct

/-!
# `Taylm.representsa_point` is sufficient

When the test holds, and every remainder is a nonempty interval, the range set of the models is
the one point, the polynomial zonotope's centre. One direction: the test is sufficient only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.construct_eq_of_representsa_point (T : Fin m → Taylm n)
    (hT : ∀ i, (T i).remInf ≤ (T i).remSup) (h : Taylm.representsa_point T) :
    Taylm.construct T = {(Taylm.polyZonotope T).c} := by
  rw [← Taylm.polyZonotope_exact T hT]
  exact PolyZonotope.construct_eq_of_representsa_point _ h


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

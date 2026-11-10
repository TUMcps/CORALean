module

public import CORALean.ContSet.Taylm.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RepresentsaPointToSet
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmPolyZonotopeExact

@[expose] public section

/-!
# `Taylm.representsa_point` is sufficient

When the test holds, and every remainder is a nonempty interval, the range set of the models is
the one point, the polynomial zonotope's center. One direction: the test is sufficient only.

## Inputs
* `T` – family of Taylor models

## Hypotheses
* `hT` – each remainder is an ordered interval
* `h` – the point test holds

## Conclusion
* the range set is the point of the constant terms
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.toSet_eq_of_representsa_point (T : Fin m → Taylm n)
    (hT : ∀ i, (T i).rem.inf ≤ (T i).rem.sup) (h : Taylm.representsa_point T) :
    Taylm.toSet T = {(Taylm.polyZonotope T).c} := by
  rw [← Taylm.polyZonotope_exact T hT]
  exact PolyZonotope.toSet_eq_of_representsa_point _ h


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

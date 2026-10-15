module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.allTerms (T : Fin m → Taylm n) : List (Fin m × (ℝ × (Fin n → ℕ))) :=
  (List.finRange m).flatMap fun i => (T i).terms.map fun a => (i, a)

noncomputable def Taylm.polyZonotope (T : Fin m → Taylm n) : PolyZonotope (Vec ℝ m) where
  p := n
  h := (Taylm.allTerms T).length
  q := m
  c := fun i => ((T i).rem.inf + (T i).rem.sup) / 2
  G := fun j => Pi.single ((Taylm.allTerms T).get j).1 ((Taylm.allTerms T).get j).2.1
  E := fun k j => ((Taylm.allTerms T).get j).2.2 k
  GI := fun l => Pi.single l (((T l).rem.sup - (T l).rem.inf) / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A box as halfspaces

## Inputs
* `I` – interval

## Output
* halfspace polytope of the box
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.hPolytope (I : Interval (Vec ℝ n)) : HPolytope (Vec ℝ n) where
  m := n + n
  A := Fin.append (fun j => LinearMap.proj j) (fun j => -LinearMap.proj j)
  b := Fin.append I.sup fun j => -I.inf j
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

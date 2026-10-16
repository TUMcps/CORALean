module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.unitBox`

The supremum-norm unit ball as `2n` constraints, `±xⱼ ≤ 1`. This is the
coefficient domain a zonotope ranges over, so a constrained zonotope's domain is
this intersected with its constraints.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.unitBox (n : ℕ) : HPolytope (Vec ℝ n) where
  m := n + n
  A := Fin.append (fun j => LinearMap.proj j) (fun j => -LinearMap.proj j)
  b := fun _ => 1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

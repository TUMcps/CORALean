import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.unitBox`

The supremum-norm unit ball as `2n` constraints, `±xⱼ ≤ 1`. This is the
coefficient domain a zonotope ranges over, so a constrained zonotope's domain is
this intersected with its constraints.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def HPolytope.unitBox (n : ℕ) : HPolytope (Vec ℝ n) where
  m := n + n
  A := Fin.append (fun j => LinearMap.proj j) (fun j => -LinearMap.proj j)
  b := fun _ => 1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real

import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.ofPoint`

Not the zero-generator case every other representation's singleton is: a
halfspace description has no generators to drop, only rows to add, so a
point costs `n` equality constraints, one per coordinate — why this
representation was the one left without an `OfPoint` in the earlier round.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as `n` equality rows and no inequalities: coordinate `i`
pinned by `LinearMap.proj i`, the only route in at this representation. -/
def HPolytope.ofPoint (v : Vec ℝ n) : HPolytope (Vec ℝ n) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := n
  Ae := fun i => LinearMap.proj i
  be := v

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

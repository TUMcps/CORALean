import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.Module.Prod

/-!
# `ConZonotope.stack`

The zonotope `zonotope([c; 0], [G; A])` of CORA's `@conZonotope/contains_` (`aux_containsPoint`):
the generators stacked over the constraint rows of `A`, so that the last `q` coordinates of a
point `c + G β` read `A β`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope([c; 0], [G; A])`: the generators stacked over the constraint rows. -/
def ConZonotope.stack (c : Vec ℝ n) (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) :
    Zonotope (Vec ℝ n × Vec ℝ q) where
  h := h
  c := (c, 0)
  G := fun j => (G j, fun i => A i j)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

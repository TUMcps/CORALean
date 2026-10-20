module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `ConZonotope.stack`

The zonotope `zonotope([c; 0], [G; A])` of CORA's `@conZonotope/contains_` (`aux_containsPoint`):
the generators stacked over the constraint rows of `A`, so that the last `q` coordinates of a
point `c + G β` read `A β`.

## Inputs
* `c` – center
* `G` – generators
* `A` – constraint matrix

## Output
* the zonotope stacking the constraint rows under the generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

module

public import CORALean.ContSet.ConZonotope.Real.Operations.Stack

@[expose] public section

/-!
# `ConZonotope.containsPoint`

The point branch of CORA's `@conZonotope/contains_` (`aux_containsPoint`, method `'exact'`, no
scaling factor requested): `p` is contained exactly when the stacked point `[p; b]` lies in the
stacked zonotope `ConZonotope.stack`. CORA hands the question to the zonotope's `contains_`, a
linear program; here it is the membership that program decides.

## Inputs
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `p` – point to test

## Output
* the point lies in the constrained zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` is contained: `[p; b]` lies in the stacked zonotope. -/
def ConZonotope.containsPoint (c : Vec ℝ n) (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) (b : Vec ℝ q)
    (p : Vec ℝ n) : Prop :=
  (p, b) ∈ (ConZonotope.stack c G A).construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

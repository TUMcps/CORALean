module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# AH-polytopes

`[1, Def. 2]`: an affine image `x̄ + X P` of an H-polytope `P ⊂ ℝ^m`, the form in which a
zonotope (`P` the unit box), a projection, a Minkowski sum and a convex hull of
H-polytopes are all cheap to write down and expensive to put back into halfspaces.
A set, not a representation: `ConZonotope` is the representation, and
`ConZonotope.eq_construct_iff_isAffineImage` says the two describe the same sets.

## Inputs
* `xbar` – mean of length `n`
* `X` – `n × m` matrix
* `P` – H-polytope

## Output
* `x̄ + X P`, `[1, Def. 2]`

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC), 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x̄ + X P`, `[1, Def. 2]`. -/
def HPolytope.ahPolytope (xbar : Vec ℝ n) (X : Mat ℝ n m) (P : HPolytope (Vec ℝ m)) :
    Set (Vec ℝ n) :=
  {x | ∃ p ∈ P.construct, x = xbar + X *ᵥ p}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

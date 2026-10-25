module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.ContainsMat`

CORA's `@matZonotope/contains`: `contains(zonotope(matZ), reshape(S, n*m, p))`, the `p` matrices of
`S` stacked into points of the vector zonotope. Written as membership of every matrix. CORA's
tolerance (default `1e-12`, which widens a non-full-dimensional zonotope by a box) and its
`'approx'` type are not modelled.

## Inputs
* `Z` – matrix zonotope
* `S` – family of matrices

## Output
* `Prop` that every matrix of `S` lies in `Z`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every matrix of `S` lies in the matrix zonotope. -/
def Zonotope.ContainsMat (Z : Zonotope (Mat ℝ m n)) (S : Fin p → Mat ℝ m n) : Prop :=
  ∀ k, S k ∈ Z.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

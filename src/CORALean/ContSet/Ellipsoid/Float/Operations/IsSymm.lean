module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Ellipsoid.isSymm`: the shape matrix is symmetric, exactly

CORA's constructor accepts a shape matrix `Q` that passes `isApproxSymmetric(Q, TOL)`
(`@ellipsoid/ellipsoid.m`, l. 161), symmetric up to a tolerance. Here the test is exact, `Q i j =
Q j i` at every pair, which is the stricter one, so what it accepts CORA accepts. The scalar
interface has no exact equality, and needs none: `le` constrains a `true` answer only, `a ≤ b` and
`b ≤ a` make `a = b`, and the loop visits both `(i, j)` and `(j, i)`, so `le (Q i j) (Q j i)` at
every pair is `Q i j = Q j i` at every pair (`Theorems/SymmOfIsSymm`).

## Inputs
* `Q` – shape matrix

## Output
* `true` only if `Q` is symmetric
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stored matrix is symmetric: `le` at every pair `(i, j)` in the one direction, which over
all pairs is both. -/
def Ellipsoid.isSymm (Q : Mat 𝕋 n n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j => le (Q i j) (Q j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

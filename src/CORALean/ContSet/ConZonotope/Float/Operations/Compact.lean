module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
public import CORALean.ContSet.HPolytope.Float.Operations.SelectCols

@[expose] public section

/-!
# `ConZonotope.compact` over a floating-point scalar

CORA's `@conZonotope/compact_` with method `'zeros'` (also what `'all'` does) on the stored floats:
delete the generators whose column of `[G; A; Ae]` is zero, then the zero constraint rows. Both
steps on the constraint are its own operations (#174): `HPolytope.isZeroCol`,
`HPolytope.selectCols`, and `HPolytope.dropZeros`, which deletes the zero rows that hold (`0 x = be`
with `be = 0`, and `0 ≤ b`) and returns the empty polytope when a zero row is certified infeasible.
A row or column goes only when every entry is certified zero by `le` both ways, so nothing rounds
but that infeasibility test, and the set is the same (`compact_exact`). The order is kept. Tolerance
`0`; CORA's `eps` removes columns below it as well.

## Inputs
* `cZ` – float constrained zonotope

## Output
* the set without zero generators and zero constraint rows
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.compact (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- the generators kept: some entry of the column of `[G; A; Ae]` not certified zero
  let S := Finset.univ.filter fun j : Fin cZ.h =>
    !(HPolytope.isZeroVec (cZ.G j) && cZ.P.isZeroCol j)
  { h := S.card
    c := cZ.c
    G := fun l => cZ.G (S.orderEmbOfFin rfl l)
    -- the rows on the kept coefficients, the zero rows dropped
    P := (cZ.P.selectCols (S.orderEmbOfFin rfl)).dropZeros
    I_error := cZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

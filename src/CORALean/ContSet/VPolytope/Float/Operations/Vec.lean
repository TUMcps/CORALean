module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Interval.Float.Operations.Vec

@[expose] public section

/-!
# `VPolytope.vec`, over a floating-point scalar

CORA's `polytope(matP)`: every vertex matrix and the error box stacked column by column, entry
`(i, j)` going to position `i + m * j`. Entries are moved, not computed, so nothing rounds.

## Inputs
* `P` – matrix polytope

## Output
* polytope of the stacked vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each vertex and the box stacked column-major. -/
def VPolytope.vec (P : VPolytope (Mat 𝕋 m n)) : VPolytope (Vec 𝕋 (n * m)) where
  k := P.k
  V := fun l k => P.V l (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  I_error := P.I_error.vec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

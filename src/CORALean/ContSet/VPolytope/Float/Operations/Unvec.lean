module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Interval.Float.Operations.Unvec

@[expose] public section

/-!
# `VPolytope.unvec`, over a floating-point scalar

The inverse of `VPolytope.vec`: every stacked vertex and the error box reshaped back into
matrices. Entries are moved, not computed, so nothing rounds.

## Inputs
* `P` – polytope of stacked vertices

## Output
* matrix polytope of the unstacked vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each vertex and the box unstacked. -/
def VPolytope.unvec (P : VPolytope (Vec 𝕋 (n * m))) : VPolytope (Mat 𝕋 m n) where
  k := P.k
  V := fun l i j => P.V l (finProdFinEquiv (j, i))
  I_error := P.I_error.unvec

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

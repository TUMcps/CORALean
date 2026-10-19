module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.center`

CORA's `center` with method `'avg'`: `c = mean(V, 2)`, the mean of the vertices. `vertices(P)`
of a polytope given by vertices first removes the redundant ones (`compact_(P, 'V', tol)`) unless
`minVRep` is already known, so this is CORA's result when the stored vertices are the extreme
points. The default method `'chebyshev'` (a linear program) is not here.

## Inputs
* `P` – polytope

## Output
* mean of the vertices
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.center (P : VPolytope α) : α := (1 / (P.k : ℝ)) • ∑ j, P.V j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

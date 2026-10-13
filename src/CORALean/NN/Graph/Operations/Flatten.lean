import CORALean.ContSet.ContSet.ContSet

/-!
# A node-feature matrix as one vector

A graph layer's input `H : Mat α N F` stacked row by row into a `Vec α (N * F)`, the shape a float
polynomial zonotope has (`Float.PolyZonotope` is vector-shaped). Node `i`, feature `j` sits at
`finProdFinEquiv (i, j)`. Generic over the entry type, so it flattens a real matrix and a float one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `H` stacked row by row. -/
def GNN.flatten (H : Mat α N F) : Vec α (N * F) :=
  fun r => H (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

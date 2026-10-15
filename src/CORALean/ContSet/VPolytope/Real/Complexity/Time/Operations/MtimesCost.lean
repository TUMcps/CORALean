module

public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends each of the `k` vertices
through `M *ᵥ ·`, one matrix-vector product per vertex, each writing its result inside
`Cost.matVec`, and nothing
else.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `VPolytope.mtimes` costs at `M : Mat ℝ m n` and `k` vertices: one
matrix-vector product per vertex. -/
def VPolytope.mtimesCost (m n k : ℕ) : Cost := k • Cost.matVec m n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

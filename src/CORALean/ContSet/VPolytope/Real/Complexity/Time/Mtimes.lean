module

public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends each of the `k` vertices
through `M *ᵥ ·`, one matrix-vector product per vertex and nothing else.
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

/-- Monotone in the vertex count, so a bound on the operand's size gives a
bound on the cost. -/
theorem VPolytope.mtimesCost_mono {k k' : ℕ} (m n : ℕ) (hle : k ≤ k') :
    VPolytope.mtimesCost m n k ≤ VPolytope.mtimesCost m n k' :=
  Nat.mul_le_mul_right _ hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

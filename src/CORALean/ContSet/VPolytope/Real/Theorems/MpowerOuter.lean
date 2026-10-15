module

public import CORALean.ContSet.VPolytope.Real.Operations.Mpower
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint

@[expose] public section

/-!
# `VPolytope.mpower` encloses the powers of every member

The identity for the zero power, the polytope for the first, and `matMul_outer` for each further
factor on the right: `M ^ (k + 2) = M ^ (k + 1) * M`. An enclosure only, the vertex products being a
superset.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every power `M ^ k` of a member lies in the `k`-th matrix-polytope power. -/
theorem VPolytope.mpower_outer (P : VPolytope (Mat ℝ n n)) {M : Mat ℝ n n} (hM : M ∈ P.construct)
    (k : ℕ) : M ^ k ∈ (VPolytope.mpower P k).construct := by -- --- PROOF ---
  rcases k with _ | k
  · rw [pow_zero]
    show 1 ∈ (VPolytope.point (1 : Mat ℝ n n)).construct
    rw [VPolytope.construct_point]
    rfl
  · induction k with
    | zero => rw [zero_add, pow_one]; exact hM
    | succ k ih =>
      rw [pow_succ]
      exact VPolytope.matMul_outer _ P ih hM

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

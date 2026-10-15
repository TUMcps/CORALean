module

public import CORALean.ContSet.Zonotope.Real.Operations.Mpower
public import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct

@[expose] public section

/-!
# `Zonotope.mpower` encloses the powers of every member

The identity for the zero power, the zonotope for the first, and `matMul_outer` for each further
factor on the right: `M ^ (k + 2) = M ^ (k + 1) * M`. An enclosure only, `matMul` keeping every
cross term free.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every power `M ^ k` of a member lies in the `k`-th matrix-zonotope power. -/
theorem Zonotope.mpower_outer (Z : Zonotope (Mat ℝ n n)) {M : Mat ℝ n n} (hM : M ∈ Z.construct)
    (k : ℕ) : M ^ k ∈ (Zonotope.mpower Z k).construct := by -- --- PROOF ---
  rcases k with _ | k
  · rw [pow_zero]
    exact Zonotope.centre_mem_construct (Zonotope.ofPoint 1)
  · induction k with
    | zero => rw [zero_add, pow_one]; exact hM
    | succ k ih =>
      rw [pow_succ]
      exact Zonotope.matMul_outer _ Z (Set.mem_iUnion₂.mpr ⟨_, ih, Set.mem_image_of_mem _ hM⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

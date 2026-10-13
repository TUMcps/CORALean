module

public import CORALean.ContSet.VPolytope.Real.Operations.MtimesMatPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.BilinOuter

@[expose] public section

/-!
# A matrix polytope times a vertex set encloses every matrix's image

`bilin_outer` at `Matrix.mulVecBilin`, once that bilinear map is known to read
back as `*ᵥ`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mtimesMatPolytope_outer (M : VPolytope (Mat ℝ m n)) (P : VPolytope (Vec ℝ n)) :
    (⋃ A ∈ M.construct, (A *ᵥ ·) '' P.construct)
      ⊆ (VPolytope.mtimesMatPolytope M P).construct := by
  -- binding `h` first: against this goal's expected type, `isDefEq` never terminates
  have h := VPolytope.bilin_outer (Matrix.mulVecBilin ℝ ℝ) M P
  simp only [VPolytope.mtimesMatPolytope, ← Matrix.mulVecBilin_apply ℝ ℝ]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

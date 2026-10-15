module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree

@[expose] public section

/-!
# `HPolytope.intersection` is exact when both boxes are certified empty of error

Then the rows are only stacked, and a point satisfies the stacked rows exactly when it satisfies
each half (`HPolytope.mem_stackRows_construct_iff`), each polytope denoting its nominal part.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_exact {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)}
    (h₁ : P₁.isErrFree = true) (h₂ : P₂.isErrFree = true) :
    P₁.construct ∩ P₂.construct = (P₁.intersection P₂).construct := by
  rw [HPolytope.intersection, if_pos (by rw [h₁, h₂]; rfl)]
  exact Set.ext fun _ => (HPolytope.mem_stackRows_construct_iff
    (HPolytope.errFree_of_isErrFree h₁) (HPolytope.errFree_of_isErrFree h₂)).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

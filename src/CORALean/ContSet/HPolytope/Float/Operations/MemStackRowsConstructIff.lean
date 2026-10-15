module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# Membership in `HPolytope.stackRows` of error-free polytopes

Without boxes the nominal parts are the sets, so membership splits over the sets themselves.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_stackRows_construct_iff {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n}
    (h₁ : P₁.ErrFree) (h₂ : P₂.ErrFree) :
    x ∈ (P₁.stackRows P₂).construct ↔ x ∈ P₁.construct ∧ x ∈ P₂.construct := by
  rw [HPolytope.mem_stackRows_iff, HPolytope.construct_eq_nominal h₁,
    HPolytope.construct_eq_nominal h₂]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

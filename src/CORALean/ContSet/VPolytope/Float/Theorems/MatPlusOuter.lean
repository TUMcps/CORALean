module

public import CORALean.ContSet.VPolytope.Float.Operations.MatPlus
public import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.UnvecExact

@[expose] public section

/-!
# `VPolytope.matPlus` over-approximates the Minkowski sum

The Minkowski sum of the stacked operands lies in the stacked sum (`VPolytope.plus_outer`), and
stacking and unstacking are exact, so the sum of two members lies in the matrix polytope of the
pairwise sums.

## Inputs
* `P₁` – first matrix polytope
* `P₂` – second matrix polytope

## Hypotheses
* none

## Conclusion
* the Minkowski sum lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.matPlus_outer (P₁ P₂ : VPolytope (Mat 𝕋 m n)) : -- --- CONCL ---
    InflatedContSet.construct P₁ + InflatedContSet.construct P₂ ⊆
      InflatedContSet.construct (P₁.matPlus P₂) := by -- --- PROOF ---
  rintro _ ⟨A, hA, B, hB, rfl⟩
  -- the stacked operands are in the stacked polytopes
  have hA' : matVecEquiv A ∈ InflatedContSet.construct P₁.vec := by
    rw [VPolytope.vec_exact]; exact ⟨A, hA, rfl⟩
  have hB' : matVecEquiv B ∈ InflatedContSet.construct P₂.vec := by
    rw [VPolytope.vec_exact]; exact ⟨B, hB, rfl⟩
  -- so their sum is in the stacked pairwise sums
  have h1 : matVecEquiv A + matVecEquiv B ∈ (P₁.vec.plus P₂.vec).construct :=
    VPolytope.plus_outer P₁.vec P₂.vec ⟨_, hA', _, hB', rfl⟩
  rw [VPolytope.matPlus, VPolytope.unvec_exact]
  exact ⟨_, h1, by simp⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

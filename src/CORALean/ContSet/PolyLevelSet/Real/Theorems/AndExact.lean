module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `PolyLevelSet.and_` is exact

Stacking the rows is intersecting the sets, whatever the operators: a row of either operand reads
only its own monomials, the other block of its coefficients being zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacked rows denote the intersection of the two sets. -/
theorem PolyLevelSet.and_exact (P₁ P₂ : PolyLevelSet n) :
    (P₁.and_ P₂).construct = P₁.construct ∩ P₂.construct := by -- --- PROOF ---
  ext x
  -- the stacked monomial vector is the two operands' side by side
  have hμ : PolyZonotope.monomial (P₁.and_ P₂).R x
      = Fin.append (PolyZonotope.monomial P₁.R x) (PolyZonotope.monomial P₂.R x) := by
    refine funext (Fin.addCases (fun j => ?_) fun j => ?_) <;>
      simp [PolyZonotope.monomial, PolyLevelSet.and_]
  have hrow : (P₁.and_ P₂).A *ᵥ PolyZonotope.monomial (P₁.and_ P₂).R x - (P₁.and_ P₂).b
      = Fin.append (P₁.A *ᵥ PolyZonotope.monomial P₁.R x - P₁.b)
          (P₂.A *ᵥ PolyZonotope.monomial P₂.R x - P₂.b) := by
    rw [hμ]
    -- a row of either operand meets its own monomials alone
    refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
    · rw [Fin.append_left]
      show ((P₁.and_ P₂).A *ᵥ Fin.append (PolyZonotope.monomial P₁.R x)
            (PolyZonotope.monomial P₂.R x)) (Fin.castAdd P₂.m i) - Fin.append P₁.b P₂.b
            (Fin.castAdd P₂.m i) = (P₁.A *ᵥ PolyZonotope.monomial P₁.R x - P₁.b) i
      simp only [PolyLevelSet.and_, Matrix.mulVec, dotProduct, Pi.sub_apply, Fin.append_left,
        sub_left_inj]
      exact (Fin.sum_univ_add _).trans (by simp)
    · rw [Fin.append_right]
      show ((P₁.and_ P₂).A *ᵥ Fin.append (PolyZonotope.monomial P₁.R x)
            (PolyZonotope.monomial P₂.R x)) (Fin.natAdd P₁.m i) - Fin.append P₁.b P₂.b
            (Fin.natAdd P₁.m i) = (P₂.A *ᵥ PolyZonotope.monomial P₂.R x - P₂.b) i
      simp only [PolyLevelSet.and_, Matrix.mulVec, dotProduct, Pi.sub_apply, Fin.append_right,
        sub_left_inj]
      exact (Fin.sum_univ_add _).trans (by simp)
  show (∀ i, ((P₁.and_ P₂).op i).holds _) ↔ _
  rw [hrow]
  exact LevelSet.forall_append_holds _ _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

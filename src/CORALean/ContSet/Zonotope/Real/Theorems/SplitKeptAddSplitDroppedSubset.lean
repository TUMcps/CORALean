import CORALean.ContSet.Zonotope.Real.Operations.SplitKept
import CORALean.ContSet.Zonotope.Real.Operations.SplitDropped
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Abel

/-!
# `Z_a ⊕ Z_b ⊆ Z`

The two parts of a split sum to `Z`, [1, Sec. IV-B, Step 1)] and Sec. IV-D: `Z = Z_a ⊕ Z_b`, of
which only `⊇` is used. Each part's coefficients are read back onto `Z`'s own indices.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
open Pointwise
variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Minkowski sum of the two parts of a split is inside `Z`. -/
theorem Zonotope.splitKept_add_splitDropped_subset (Z : Zonotope α) {q r : ℕ}
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    (Z.splitKept part).construct + (Z.splitDropped part).construct
      ⊆ Z.construct := by -- --- PROOF ---
  -- the coefficients of the two parts, read back onto `Z`'s own indices
  rintro _ ⟨_, ⟨βa, hβa, rfl⟩, _, ⟨βb, hβb, rfl⟩, rfl⟩
  change Fin q → ℝ at βa
  change Fin r → ℝ at βb
  refine ⟨fun j => Sum.elim βa βb (Pair.equivSum (Fin q) (Fin r) (part.index.symm j)),
    fun j => ?_, ?_⟩
  · show |Sum.elim βa βb (Pair.equivSum (Fin q) (Fin r) (part.index.symm j))| ≤ 1
    rcases h : Pair.equivSum (Fin q) (Fin r) (part.index.symm j) with l | l
    · exact hβa l
    · exact hβb l
  · have hl : ∀ l : Fin q, Sum.elim βa βb (Pair.equivSum (Fin q) (Fin r)
        (part.index.symm (part.left l))) = βa l := fun l => by
      simp only [Partition.left, Partition.on, Equiv.symm_apply_apply]; rfl
    have hr : ∀ l : Fin r, Sum.elim βa βb (Pair.equivSum (Fin q) (Fin r)
        (part.index.symm (part.right l))) = βb l := fun l => by
      simp only [Partition.right, Partition.on, Equiv.symm_apply_apply]; rfl
    rw [part.sum_split₂ fun j => Sum.elim βa βb (Pair.equivSum (Fin q) (Fin r)
      (part.index.symm j)) • Z.G j]
    simp only [hl, hr, Zonotope.splitKept, Zonotope.splitDropped, zero_add]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

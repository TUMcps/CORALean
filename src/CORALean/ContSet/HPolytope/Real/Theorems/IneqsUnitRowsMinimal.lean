module

public import CORALean.ContSet.HPolytope.Real.Theorems.ExistsPosStepStrict
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.DropIdx
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# Distinct unit rows with offset one are all non-redundant

[1, Alg. 3], Step 2: "since the simplex is chosen such that a unit ball fits tightly inside, any
direction `ℓ` of unit length and with an associated offset of `1` will be non-redundant". That
needs `ℓ` to differ from the rows already there (`simplexRows_redundant_counterexample`). With
pairwise distinct unit rows it holds for every row: `A(j,·)` itself satisfies every other row
strictly, `A(i,·) A(j,·) < 1` for distinct unit vectors, so a small step past it along `A(j,·)`
breaks row `j` alone.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_unit_rows_minimal (A : Mat ℝ q n) (hA : ∀ i, A i ⬝ᵥ A i = 1)
    (hinj : Function.Injective A) (j : Fin q) :
    (HPolytope.ineqs A 1).construct ≠
      (HPolytope.ineqs (A.submatrix (dropIdx j) id)
        fun i => (1 : Vec ℝ q) (dropIdx j i)).construct := by -- --- PROOF ---
  -- distinct unit vectors: `aᵢ · aⱼ < 1`
  have hlt : ∀ i, i ≠ j → A i ⬝ᵥ A j < 1 := fun i hij => by
    have hne : A i - A j ≠ 0 := sub_ne_zero.mpr fun h => hij (hinj h)
    have hnn : 0 ≤ (A i - A j) ⬝ᵥ (A i - A j) := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hpos : 0 < (A i - A j) ⬝ᵥ (A i - A j) := by
      rcases hnn.eq_or_lt with h | h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hne
      · exact h
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hA, hA, dotProduct_comm (A j)] at hpos
    linarith
  have hne : ∀ i, dropIdx j i ≠ j := fun i h => by
    have := insertIdx_dropIdx j true (fun _ => false) i
    rw [h, insertIdx_self] at this
    exact Bool.noConfusion this
  -- the other rows hold strictly at `A(j,·)`, so also a little beyond it
  obtain ⟨s, hs, hstep⟩ := HPolytope.exists_pos_step_strict (A.submatrix (dropIdx j) id)
    (fun i => (1 : Vec ℝ q) (dropIdx j i)) (A j) (A j)
    (fun i => by
      show A (dropIdx j i) ⬝ᵥ A j < 1
      exact hlt _ (hne i))
  intro heq
  have hmem : A j + s • A j ∈ (HPolytope.ineqs (A.submatrix (dropIdx j) id)
      fun i => (1 : Vec ℝ q) (dropIdx j i)).construct :=
    HPolytope.mem_ineqs_iff.mpr fun i => (hstep i).le
  rw [← heq] at hmem
  have hrow := HPolytope.mem_ineqs_iff.mp hmem j
  have : (A *ᵥ (A j + s • A j)) j = 1 + s := by
    show A j ⬝ᵥ (A j + s • A j) = 1 + s
    rw [dotProduct_add, dotProduct_smul, hA, smul_eq_mul, mul_one]
  rw [this] at hrow
  simp at hrow
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

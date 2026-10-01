import CORALean.Global.Tensor
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Block-diagonal matrices

Two square matrices laid out along the diagonal of one, the zero block given
explicitly so that a float scalar, which has no `Zero` instance, can use it too.
Written once over the entry type: at `ℝ` and zero it is Mathlib's
`fromBlocks M 0 0 N` read through `finSumFinEquiv`, and `posSemidef_blockDiag_iff`
says what a linear matrix inequality needs of it, that a block-diagonal matrix is
positive semidefinite exactly when each block is.

The linearity laws are what let a sum of block-diagonal matrices be read as the
block-diagonal matrix of the sums, which is how `SpectraShadow.plus` keeps its
linear matrix inequality exact.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


def blockDiag {R : Type} (z : R) {a b : ℕ} (M : Mat R a a) (N : Mat R b b) :
    Mat R (a + b) (a + b) :=
  fun i j =>
    Fin.addCases (motive := fun _ => R)
      (fun p => Fin.addCases (motive := fun _ => R) (fun q => M p q) (fun _ => z) j)
      (fun p => Fin.addCases (motive := fun _ => R) (fun _ => z) (fun q => N p q) j) i

section Entries

variable {R : Type} (z : R) {a b : ℕ} (M : Mat R a a) (N : Mat R b b)

@[simp] theorem blockDiag_castAdd_castAdd (p q : Fin a) :
    blockDiag z M N (Fin.castAdd b p) (Fin.castAdd b q) = M p q := by simp [blockDiag]

@[simp] theorem blockDiag_castAdd_natAdd (p : Fin a) (q : Fin b) :
    blockDiag z M N (Fin.castAdd b p) (Fin.natAdd a q) = z := by simp [blockDiag]

@[simp] theorem blockDiag_natAdd_castAdd (p : Fin b) (q : Fin a) :
    blockDiag z M N (Fin.natAdd a p) (Fin.castAdd b q) = z := by simp [blockDiag]

@[simp] theorem blockDiag_natAdd_natAdd (p q : Fin b) :
    blockDiag z M N (Fin.natAdd a p) (Fin.natAdd a q) = N p q := by simp [blockDiag]

end Entries


-- =======================================  MAIN THEOREM  ======================================= --

section Real

variable {a b : ℕ}

/-- Four cases on the two indices, which every entrywise law below is. -/
theorem blockDiag_ext {M M' : Mat ℝ (a + b) (a + b)}
    (h₁ : ∀ p q : Fin a,
      M (Fin.castAdd b p) (Fin.castAdd b q) = M' (Fin.castAdd b p) (Fin.castAdd b q))
    (h₂ : ∀ (p : Fin a) (q : Fin b),
      M (Fin.castAdd b p) (Fin.natAdd a q) = M' (Fin.castAdd b p) (Fin.natAdd a q))
    (h₃ : ∀ (p : Fin b) (q : Fin a),
      M (Fin.natAdd a p) (Fin.castAdd b q) = M' (Fin.natAdd a p) (Fin.castAdd b q))
    (h₄ : ∀ p q : Fin b,
      M (Fin.natAdd a p) (Fin.natAdd a q) = M' (Fin.natAdd a p) (Fin.natAdd a q)) :
    M = M' := by -- --- PROOF ---
  ext i j
  -- split each index into its first block or its second
  refine Fin.addCases (fun p => ?_) (fun p => ?_) i <;>
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · exact h₁ p q
  · exact h₂ p q
  · exact h₃ p q
  · exact h₄ p q

-- the linearity laws, each a case split on the four blocks

theorem blockDiag_zero : blockDiag (0 : ℝ) (0 : Mat ℝ a a) (0 : Mat ℝ b b) = 0 :=
  blockDiag_ext (by simp) (by simp) (by simp) (by simp)

theorem blockDiag_add (M₁ M₂ : Mat ℝ a a) (N₁ N₂ : Mat ℝ b b) :
    blockDiag 0 (M₁ + M₂) (N₁ + N₂) = blockDiag 0 M₁ N₁ + blockDiag 0 M₂ N₂ :=
  blockDiag_ext (by simp) (by simp) (by simp) (by simp)

theorem blockDiag_smul (t : ℝ) (M : Mat ℝ a a) (N : Mat ℝ b b) :
    blockDiag 0 (t • M) (t • N) = t • blockDiag 0 M N :=
  blockDiag_ext (by simp) (by simp) (by simp) (by simp)

theorem blockDiag_sum {ι : Type} (s : Finset ι) (M : ι → Mat ℝ a a)
    (N : ι → Mat ℝ b b) :
    blockDiag 0 (∑ i ∈ s, M i) (∑ i ∈ s, N i)
      = ∑ i ∈ s, blockDiag 0 (M i) (N i) := by -- --- PROOF ---
  classical
  induction s using Finset.induction_on with
  | empty => simpa using blockDiag_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
      blockDiag_add, ih]

/-- A block-diagonal matrix is Mathlib's `fromBlocks` on the sum index. -/
theorem blockDiag_eq_submatrix (M : Mat ℝ a a) (N : Mat ℝ b b) :
    blockDiag 0 M N =
      (fromBlocks M 0 0 N).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  refine blockDiag_ext ?_ ?_ ?_ ?_ <;> intros <;> simp

/-- The two blocks of a positive semidefinite block-diagonal matrix are, and
conversely, as the quadratic form splits along the diagonal. -/
theorem posSemidef_fromBlocks_zero_iff (M : Mat ℝ a a) (N : Mat ℝ b b) :
    (fromBlocks M 0 0 N).PosSemidef ↔ M.PosSemidef ∧ N.PosSemidef := by -- --- PROOF ---
  constructor
  -- a principal submatrix of a positive semidefinite matrix is one
  · intro h
    have e₁ : (fromBlocks M 0 0 N).submatrix Sum.inl Sum.inl = M := by ext; simp
    have e₂ : (fromBlocks M 0 0 N).submatrix Sum.inr Sum.inr = N := by ext; simp
    exact ⟨e₁ ▸ h.submatrix Sum.inl, e₂ ▸ h.submatrix Sum.inr⟩
  -- and the quadratic form of a block diagonal is the sum of the blocks'
  · rintro ⟨hM, hN⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (IsHermitian.fromBlocks hM.isHermitian (by simp) hN.isHermitian) fun x => ?_
    have hx : x = Sum.elim (fun i => x (Sum.inl i)) (fun j => x (Sum.inr j)) := by
      ext (i | j) <;> simp
    have h1 := hM.dotProduct_mulVec_nonneg (fun i => x (Sum.inl i))
    have h2 := hN.dotProduct_mulVec_nonneg (fun j => x (Sum.inr j))
    rw [hx]
    simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr, star_trivial] at h1 h2 ⊢
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
    linarith

theorem posSemidef_blockDiag_iff (M : Mat ℝ a a) (N : Mat ℝ b b) :
    (blockDiag 0 M N).PosSemidef ↔ M.PosSemidef ∧ N.PosSemidef := by
  rw [blockDiag_eq_submatrix, posSemidef_submatrix_equiv, posSemidef_fromBlocks_zero_iff]

end Real

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

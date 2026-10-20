module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# H-matrices

[1, Def. 4.7]: the comparison matrix `⟨A⟩` of an interval matrix, mignitudes on the diagonal
and minus magnitudes off it; [1, Def. 4.8]: `A` is an H-matrix if `⟨A⟩ u > 0` for some
`u > 0`. Both are written in the mignitudes `mig` and magnitudes `mag` alone, which is all of
the interval matrix the definition reads.

## Inputs
* `mig` – matrix of mignitudes
* `mag` – matrix of magnitudes

## Output
* the proposition that some positive vector makes the comparison matrix positive

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Finset

variable {k : ℕ}


/-- `(⟨A⟩ u)ᵢ = migᵢᵢ uᵢ - ∑_{j ≠ i} magᵢⱼ uⱼ`. -/
theorem compMat_mulVec_apply (mig mag : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (i : Fin k) :
    (Matrix.of (fun i j => if i = j then mig i i else -mag i j) *ᵥ u) i
      = mig i i * u i - ∑ j ∈ univ.erase i, mag i j * u j := by -- --- PROOF ---
  simp only [mulVec, dotProduct, Matrix.of_apply]
  rw [← add_sum_erase _ _ (mem_univ i), if_pos rfl, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [if_neg (ne_of_mem_erase hj).symm, neg_mul]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 4.8]: `∃ u > 0, ⟨A⟩ u > 0`, `⟨A⟩` of [1, Def. 4.7]. -/
def IsHMatrix (mig mag : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ u : Fin k → ℝ, (∀ i, 0 < u i) ∧
    ∀ i, 0 < (Matrix.of (fun i j => if i = j then mig i i else -mag i j) *ᵥ u) i


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Theorems.DominantDirectionsMemShortlist
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# The dominant directions can be singular

If the generators the length filter keeps all lie in a hyperplane (are orthogonal to one nonzero
`y`), then every subset the volume filter can pick spans less than `n` dimensions and the answer
is singular, whatever the remaining generators of `Z` do. The stated guarantee, a parallelotope
enclosing `Z`, then fails although `Z` may be full-dimensional: a zonotope with `n + 5` long
generators along one axis and a few short transversal ones has this shape
(`references/coverage/contSet/zonotope.md`, row `dominantDirections`).

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_det_eq_zero_of_orthogonal (Z : Zonotope (Vec ℝ n)) (a b : ℕ)
    (y : Vec ℝ n) (hy : y ≠ 0)
    (hort : ∀ j ∈ Z.dominantLengthFilter (min a (Finset.univ.filter fun j => Z.G j ≠ 0).card),
      Z.G j ⬝ᵥ y = 0) : -- --- STMT ---
    ∀ P ∈ Z.dominantDirections a b,
      P.det = 0 := by -- --- PROOF ---
  intro P (h : Z.dominantDirections a b = some P)
  obtain ⟨T, hT, rfl⟩ := Zonotope.dominantDirections_mem_shortlist Z a b P h
  -- the subset lies among the filtered generators
  have hTsub : T ∈ ((Z.dominantLengthFilter
      (min a (Finset.univ.filter fun j => Z.G j ≠ 0).card)).powersetCard n).toList := by
    unfold Zonotope.dominantShortlist at hT
    simp only at hT
    exact (List.mem_mergeSort.mp (List.mem_of_mem_take hT))
  rw [Finset.mem_toList, Finset.mem_powersetCard] at hTsub
  -- every column is orthogonal to `y`, so `Pᵀ y = 0`
  rw [← Matrix.det_transpose]
  refine (Matrix.exists_mulVec_eq_zero_iff).mp ⟨y, hy, ?_⟩
  funext k
  unfold Zonotope.generatorMatrix
  rw [dif_pos hTsub.2]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply]
  have := hort _ (hTsub.1 (Finset.orderEmbOfFin_mem T hTsub.2 k))
  simpa [dotProduct, mul_comm] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

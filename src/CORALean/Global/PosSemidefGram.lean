module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# A positive semidefinite matrix is a Gram matrix

The randomized rounding of [1, Thm. 17] and [1, Thm. 19] reads the dual certificate `X ≽ 0` as
the inner products of vectors: `X = Σₐ vₐ vₐᵀ` (`Matrix.posSemidef_iff_eq_sum_vecMulVec`),
so `X_{pq} = ⟨c_p, c_q⟩` for `c_p = (vₐ p)ₐ ∈ ℝ^d`.

## Inputs
* `ι` – index type
* `X` – matrix

## Hypotheses
* `hX` – the matrix is positive semidefinite

## Conclusion
* the matrix is the Gram matrix of vectors in a Euclidean space

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix
open scoped RealInnerProductSpace


-- =======================================  MAIN THEOREM  ======================================= --

theorem posSemidef_exists_gram {ι : Type*} [Fintype ι] {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    ∃ (d : ℕ) (c : ι → EuclideanSpace ℝ (Fin d)), ∀ p q, X p q = ⟪c p, c q⟫ := by
  obtain ⟨d, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  refine ⟨d, fun p => WithLp.toLp 2 fun a => v a p, fun p q => ?_⟩
  rw [hv, EuclideanSpace.inner_toLp_toLp]
  simp [Matrix.sum_apply, vecMulVec_apply, dotProduct, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

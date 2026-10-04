import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq
import CORALean.ContSet.Zonotope.Real.Theorems.SqNormSumEqGram
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# An upper bound on the maximum norm by duality

[1, Lemma 3]: every `λ` with `diag(λ) - GᵀG ≽ 0` (and `λ ≥ 0`) has `1ᵀ λ ≥ ⌈Z⌉²`, so the optimum
`d*` of the semidefinite program (18) does: on the box, `uᵀ GᵀG u ≤ uᵀ diag(λ) u ≤ 1ᵀ λ`. `λ ≥ 0`
is not needed, the diagonal of a positive semidefinite matrix being nonnegative.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.maxNormSq_le_of_dual (Z : Zonotope (Vec ℝ n)) (lam : Fin Z.h → ℝ)
    (hpsd : (Matrix.diagonal lam - Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k).PosSemidef) :
    Z.maxNormSq ≤ ∑ j, lam j := by -- --- PROOF ---
  have hq := hpsd.dotProduct_mulVec_nonneg
  -- each `λⱼ` is at least `‖gⱼ‖₂² ≥ 0`, the diagonal of the semidefinite matrix
  have hlam : ∀ j, 0 ≤ lam j := fun j => by
    have h := hq (Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_single] at h
    simp [dotProduct, Pi.single_apply] at h
    nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (Z.G j i)]
  refine csSup_le ⟨_, 0, fun j => by simp, rfl⟩ ?_
  rintro _ ⟨β, hβ, rfl⟩
  have h := hq β
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, ← Z.sq_norm₂_sum_eq_gram] at h
  -- `uᵀ diag(λ) u = ∑ λⱼ uⱼ² ≤ ∑ λⱼ`
  have hdiag : β ⬝ᵥ (Matrix.diagonal lam *ᵥ β) ≤ ∑ j, lam j := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_le_sum fun j _ => ?_
    have hb : β j * β j ≤ 1 := by
      have := abs_le.mp (hβ j)
      nlinarith
    nlinarith [hlam j]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

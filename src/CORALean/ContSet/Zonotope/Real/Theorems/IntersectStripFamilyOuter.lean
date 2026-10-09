import CORALean.ContSet.Zonotope.Real.Operations.IntersectStripFamily
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel

/-!
# `Zonotope.intersectStripFamily` encloses the intersection with the family of strips

[1, Lemma 1]: a point `x = c + G β` with `|H_j x - y_j| ≤ r_j` for every `j` is
`x + Σ_j λ_j (H_j x - y_j) - Σ_j λ_j (H_j x - y_j)`, and `(H_j x - y_j)_k = r_j γ_jk` with
`γ_jk ∈ [-1, 1]`, so the coefficients `β` on the old generators and `γ` on the new ones reach it.
For every set of gains `λ_j`; outer only, as the zonotope in general holds more than the
intersection.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectStripFamily_outer (H : Fin m → Mat ℝ p n) (r : Fin m → ℝ)
    (y : Fin m → Vec ℝ p) (lam : Fin m → Mat ℝ n p) (Z : Zonotope (Vec ℝ n)) :
    Z.construct ∩ {x | ∀ j k, |(H j *ᵥ x - y j) k| ≤ r j} ⊆
      (Z.intersectStripFamily H r y lam).construct := by -- --- PROOF ---
  rintro x ⟨⟨β, hβ, rfl⟩, hs⟩
  set x := Z.c + ∑ j, β j • Z.G j with hx
  -- the new coefficients: `r_j γ_jk = (H_j x - y_j)_k`
  let g : Fin m → Fin p → ℝ := fun j k => (H j *ᵥ x - y j) k / r j
  have hg : ∀ j k, |g j k| ≤ 1 := by
    intro j k
    have hi := hs j k
    have hr : 0 ≤ r j := le_trans (abs_nonneg _) hi
    by_cases h0 : r j = 0
    · simp [g, h0]
    · have hpos := lt_of_le_of_ne hr (Ne.symm h0)
      simp only [g, abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr hi
  have hgr : ∀ j k, g j k * r j = (H j *ᵥ x - y j) k := by
    intro j k
    have hi := hs j k
    by_cases h0 : r j = 0
    · have : (H j *ᵥ x - y j) k = 0 := abs_nonpos_iff.mp (h0 ▸ hi)
      simp [g, h0, this]
    · exact div_mul_cancel₀ _ h0
  let γ : Fin (m * p) → ℝ := fun q => g (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  have hγ : ∀ q, |γ q| ≤ 1 := fun q => hg _ _
  refine ⟨Fin.append β γ, ?_, ?_⟩
  · -- the coefficients stay in `[-1, 1]`
    intro j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simpa using hβ a
    · simpa using hγ a
  · -- the sum splits into the old generators and the new ones
    show x = Z.c + ∑ j, lam j *ᵥ (y j - H j *ᵥ Z.c) +
      ∑ l : Fin (Z.h + m * p), Fin.append β γ l •
        Fin.append (fun l => (1 - ∑ j, lam j * H j) *ᵥ Z.G l) (fun q =>
          r (finProdFinEquiv.symm q).1 •
            fun a => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2) l
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 : ∑ a : Fin Z.h, β a • ((1 - ∑ j, lam j * H j) *ᵥ Z.G a) =
        (1 - ∑ j, lam j * H j) *ᵥ (x - Z.c) := by
      rw [hx, add_sub_cancel_left]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
    -- the new generators give `Σ_j λ_j (H_j x - y_j)`
    have h2 : ∑ q : Fin (m * p), γ q • (r (finProdFinEquiv.symm q).1 •
        fun a => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2) =
        ∑ j, lam j *ᵥ (H j *ᵥ x - y j) := by
      rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      funext a
      simp only [Equiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hgr j k]
      simp only [γ, Equiv.symm_apply_apply]
      ring
    rw [h1, h2]
    -- `x = c + Σ λ_j (y_j - H_j c) + (I - Σ λ_j H_j)(x - c) + Σ λ_j (H_j x - y_j)`
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.sum_mulVec, Finset.sum_sub_distrib, Matrix.mulVec_sub]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

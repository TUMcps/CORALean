import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Matrix.Mul

/-!
# `‖x‖∞` as a maximum over `±eᵢ`

[1, Eq. 22]: the objective `‖x‖∞` of [1, Eq. 21] is the largest of the `2n` linear objectives
`±eᵢᵀ x`, which is what lets the paper solve `2n` linear programs instead. For `n ≥ 1`; at
`n = 0` there is no direction and `‖x‖∞ = 0`.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
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

theorem HPolytope.isGreatest_signed_unit (x : Vec ℝ n) (hn : 0 < n) :
    IsGreatest {t | ∃ (i : Fin n) (s : ℝ), (s = 1 ∨ s = -1) ∧
      t = (s • (Pi.single i 1 : Vec ℝ n)) ⬝ᵥ x} ‖x‖ := by -- --- PROOF ---
  have hdot : ∀ (i : Fin n) (s : ℝ), (s • (Pi.single i 1 : Vec ℝ n)) ⬝ᵥ x = s * x i :=
    fun i s => by rw [smul_dotProduct, single_one_dotProduct, smul_eq_mul]
  refine ⟨?_, ?_⟩
  -- some coordinate attains the maximum, with its sign
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ‖x j‖₊
    have hnorm : ‖x‖ = |x i| := by
      rw [Pi.norm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty, hi, coe_nnnorm,
        Real.norm_eq_abs]
    rcases le_total 0 (x i) with h | h
    · exact ⟨i, 1, Or.inl rfl, by rw [hdot, hnorm, abs_of_nonneg h, one_mul]⟩
    · exact ⟨i, -1, Or.inr rfl, by rw [hdot, hnorm, abs_of_nonpos h, neg_one_mul]⟩
  -- every signed coordinate is at most the norm
  · rintro t ⟨i, s, hs, rfl⟩
    rw [hdot]
    have hi := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at hi
    rcases hs with rfl | rfl
    · linarith [le_abs_self (x i)]
    · linarith [neg_abs_le (x i)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

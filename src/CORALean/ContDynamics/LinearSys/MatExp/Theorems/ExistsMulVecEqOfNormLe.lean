import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp

/-!
# A short vector is a small matrix applied to a given one

A vector `ρ` with `‖ρ‖ ≤ ‖v‖ R` is `E v` for a matrix `E` whose every entry is
within `R` of zero: put `ρ / v_{j₀}` in the column `j₀` where `v` attains its sup
norm. It is how a remainder bounded as a vector becomes the symmetric interval
matrix an exponential enclosure is widened by — the radius per entry is the
vector's bound, not `n` times it, because `Vec` carries the sup norm.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A vector no longer than `‖v‖ R` is `E v` for an `E` with entries within `R`:
put it in the column where `v` attains its sup norm. -/
theorem exists_mulVec_eq_of_norm_le {ρ v : Vec ℝ n} {R : ℝ} (hR : 0 ≤ R) (h : ‖ρ‖ ≤ ‖v‖ * R) :
    ∃ E : Mat ℝ n n, (∀ i j, |E i j| ≤ R) ∧ E *ᵥ v = ρ := by -- --- PROOF ---
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, fun i j => by simpa using hR, ?_⟩
    have : ‖ρ‖ ≤ 0 := by simpa using h
    rw [norm_le_zero_iff.mp this]; simp
  · have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at hne
      exact hv (funext fun i => (hne.false i).elim)
    -- the coordinate where `v` attains its norm, which is not zero
    obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) hn
    have hnorm : ‖v‖ = ‖v j0‖ := le_antisymm
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hj0 j (Finset.mem_univ _))
      (norm_le_pi_norm v j0)
    have hv0 : v j0 ≠ 0 := by
      intro h0; apply hv; rw [← norm_eq_zero, hnorm, h0, norm_zero]
    refine ⟨fun i j => if j = j0 then ρ i / v j0 else 0, fun i j => ?_, ?_⟩
    · show |(if j = j0 then ρ i / v j0 else 0)| ≤ R
      split_ifs
      · rw [abs_div, div_le_iff₀ (abs_pos.mpr hv0)]
        have := norm_le_pi_norm ρ i
        rw [Real.norm_eq_abs] at this
        rw [hnorm, Real.norm_eq_abs] at h
        linarith [mul_comm (|v j0|) R]
      · simpa using hR
    · funext i
      simp only [mulVec, dotProduct, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

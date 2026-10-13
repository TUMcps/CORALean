import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity

/-!
# The correction coefficient bounds `s^i - s` from below

[1, Prop. 3.1]: the correction matrix widens by the range of
`t ↦ t^i - t·r^(i-1)` over a step, whose lower end this bounds after scaling
`t = s·r` to `s^i - s` on `[0,1]` — `sub_le_zero` gives the upper end.

Proved by the tangent line at the stationary point rather than by calculus:
factoring `s^i - a^i = (Σ_k s^k a^(i-1-k))(s - a)` turns the claim into
`Σ_k s^k a^(i-1-k) ≥ 1` when `s ≥ a`, which holds because `a^(i-1) = 1/i` makes
the constant sum exactly `1`. No upper bound on `s` is needed: the stationary
point is the minimum over all of `[0,∞)`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {i : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_corrCritical_pos (hi : 2 ≤ i) : 0 < MatExp.corrCritical i :=
  Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le two_pos hi) _

theorem aux_corrCritical_le_one (hi : 2 ≤ i) : MatExp.corrCritical i ≤ 1 := by -- --- PROOF ---
  have hi1 : (1:ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.one_le_of_lt hi
  have hsub : (0:ℝ) < (i : ℝ) - 1 := by
    have : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
    linarith
  rw [MatExp.corrCritical]
  apply Real.rpow_le_one_of_one_le_of_nonpos hi1
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- The stationary point is where `a ^ (i-1) = 1/i`, which is the whole reason
the constant sum below comes to exactly `1`. -/
theorem aux_corrCritical_pow (hi : 2 ≤ i) :
    MatExp.corrCritical i ^ (i - 1) = 1 / (i : ℝ) := by -- --- PROOF ---
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  have hsub : ((i : ℝ) - 1) ≠ 0 := by linarith
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have h1 : 1 ≤ i := by omega
    push_cast [Nat.cast_sub h1]; ring
  rw [MatExp.corrCritical,
    ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) (i - 1),
    ← Real.rpow_mul hipos.le, hcast, div_mul_cancel₀ _ hsub, Real.rpow_neg_one]
  exact (one_div _).symm

/-- The form [1] states the coefficient in. -/
theorem aux_corrCoeff_eq (hi : 2 ≤ i) :
    MatExp.corrCoeff i
      = (i : ℝ) ^ (-(i:ℝ) / ((i : ℝ) - 1))
        - (i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1)) := by -- --- PROOF ---
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  rw [MatExp.corrCoeff, MatExp.corrCritical,
    ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) i, ← Real.rpow_mul hipos.le]
  ring_nf


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.corrCoeff_le_sub (hi : 2 ≤ i) {s : ℝ} (hs0 : 0 ≤ s) :
    MatExp.corrCoeff i ≤ s ^ i - s := by -- --- PROOF ---
  rw [MatExp.corrCoeff]
  set a := MatExp.corrCritical i with ha
  have hapos : 0 < a := aux_corrCritical_pos hi
  have hipos : (0:ℝ) < (i:ℝ) := by positivity
  have hpow : a ^ (i - 1) = 1 / (i:ℝ) := aux_corrCritical_pow hi
  have hfac : (∑ k ∈ Finset.range i, s ^ k * a ^ (i - 1 - k)) * (s - a) = s ^ i - a ^ i :=
    geom_sum₂_mul s a i
  have hconst : ∑ k ∈ Finset.range i, a ^ k * a ^ (i - 1 - k) = 1 := by
    have hterm : ∀ k ∈ Finset.range i, a ^ k * a ^ (i - 1 - k) = a ^ (i - 1) := by
      intro k hk
      rw [← pow_add]
      congr 1
      have : k < i := Finset.mem_range.mp hk
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hpow]
    field_simp
  -- the tangent line at `a`: the factored sum is at least 1 above `a` and at most 1 below
  have key : s - a ≤ s ^ i - a ^ i := by
    rw [← hfac]
    rcases le_total a s with hle | hle
    · have hsum : (1:ℝ) ≤ ∑ k ∈ Finset.range i, s ^ k * a ^ (i - 1 - k) := by
        rw [← hconst]
        exact Finset.sum_le_sum fun k _ => by gcongr
      exact le_mul_of_one_le_left (by linarith) hsum
    · have hsum : (∑ k ∈ Finset.range i, s ^ k * a ^ (i - 1 - k)) ≤ 1 := by
        rw [← hconst]
        exact Finset.sum_le_sum fun k _ => by gcongr
      calc s - a = 1 * (s - a) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonpos_right hsum (by linarith)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

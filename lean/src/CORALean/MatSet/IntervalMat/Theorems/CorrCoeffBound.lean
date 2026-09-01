import CORALean.MatSet.IntervalMat.Operations

/-!
# `s ^ i - s` on `[0,1]`, exactly

Althoff's thesis (2010), Prop. 3.1: the correction matrix widens by the range of
`t ↦ t^i - t·r^(i-1)` over a step, and that range is `[corrCoeff i · r^i, 0]`.
Scaling `t = s·r` leaves `s ^ i - s` on `[0,1]`, which is what is bounded here.

Proved by the tangent line at the stationary point rather than by calculus:
factoring `s^i - a^i = (Σ_k s^k a^(i-1-k))(s - a)` turns the claim into
`Σ_k s^k a^(i-1-k) ≥ 1` when `s ≥ a` and `≤ 1` when `s ≤ a`, and both hold
because `a^(i-1) = 1/i` makes the constant sum exactly `1`.

The lower bound needs no upper bound on `s`: the stationary point is the minimum
over all of `[0,∞)`. Only `s ^ i ≤ s` needs `s ≤ 1`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {i : ℕ}

set_option maxHeartbeats 40000 in
theorem aux_corrCritical_pos (hi : 2 ≤ i) : 0 < IntervalMat.corrCritical i :=
  Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le two_pos hi) _

set_option maxHeartbeats 40000 in
theorem aux_corrCritical_le_one (hi : 2 ≤ i) : IntervalMat.corrCritical i ≤ 1 := by
  have hi1 : (1:ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.one_le_of_lt hi
  have hsub : (0:ℝ) < (i : ℝ) - 1 := by
    have : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
    linarith
  rw [IntervalMat.corrCritical]
  apply Real.rpow_le_one_of_one_le_of_nonpos hi1
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

set_option maxHeartbeats 40000 in
/-- The stationary point is where `a ^ (i-1) = 1/i`, which is the whole reason
the constant sum below comes to exactly `1`. -/
theorem aux_corrCritical_pow (hi : 2 ≤ i) :
    IntervalMat.corrCritical i ^ (i - 1) = 1 / (i : ℝ) := by
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  have hsub : ((i : ℝ) - 1) ≠ 0 := by linarith
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have h1 : 1 ≤ i := by omega
    push_cast [Nat.cast_sub h1]; ring
  rw [IntervalMat.corrCritical,
    ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) (i - 1),
    ← Real.rpow_mul hipos.le, hcast, div_mul_cancel₀ _ hsub, Real.rpow_neg_one]
  exact (one_div _).symm

set_option maxHeartbeats 40000 in
/-- The form Althoff's thesis states the coefficient in. -/
theorem IntervalMat.corrCoeff_eq (hi : 2 ≤ i) :
    IntervalMat.corrCoeff i
      = (i : ℝ) ^ (-(i:ℝ) / ((i : ℝ) - 1)) - (i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1)) := by
  have hi1 : (1:ℝ) < (i : ℝ) := by exact_mod_cast hi.trans_lt' one_lt_two
  have hipos : (0:ℝ) < (i : ℝ) := by linarith
  rw [IntervalMat.corrCoeff, IntervalMat.corrCritical,
    ← Real.rpow_natCast ((i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))) i, ← Real.rpow_mul hipos.le]
  ring_nf

set_option maxHeartbeats 200000 in
theorem IntervalMat.corrCoeff_le_sub (hi : 2 ≤ i) {s : ℝ} (hs0 : 0 ≤ s) :
    IntervalMat.corrCoeff i ≤ s ^ i - s := by
  rw [IntervalMat.corrCoeff]
  set a := IntervalMat.corrCritical i with ha
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

theorem IntervalMat.sub_le_zero (hi : 1 ≤ i) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ i - s ≤ 0 := by
  have : s ^ i ≤ s ^ 1 := pow_le_pow_of_le_one hs0 hs1 hi
  simpa using this

end CORALean.Real

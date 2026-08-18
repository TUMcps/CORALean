import CORALean.Arithmetic.Real.MatSet.IntervalMat.Operations

/-!
# The interpolation error of a matrix exponential, as one series

`e^{At} - I - (t/r)(e^{Ar} - I)` is what the correction matrix has to cover:
the gap between the true flow and the straight line from `I` to `e^{Ar}`.

Written here as a single series in `A^i` starting at `i = 2`. The constant terms
cancel against `I` and `(t/r)I`, and the linear terms cancel because
`t - (t/r)r = 0` — which is why the correction is second order and why `r ≠ 0`
is needed, since at `r = 0` Lean's `t/r` is `0` and that cancellation fails.

Keeping the two exponentials in one series is what makes Althoff's `E(r)` bound
provable: the tail terms share `A^i`, so `t^i - t·r^(i-1)` is bounded once,
rather than each remainder being bounded on its own and the two added.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

set_option maxHeartbeats 200000 in
/-- The exponential of a scaled matrix, with the scalar pulled out of the power. -/
theorem aux_exp_smul_eq (A : Mat ℝ n n) (t : ℝ) :
    exp (t • A) = ∑' i : ℕ, (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i := by
  have h : exp (t • A) = ∑' i : ℕ, ((Nat.factorial i : ℝ))⁻¹ • (t • A) ^ i := by
    rw [exp_eq_tsum (𝕂 := ℝ)]
  rw [h]
  exact tsum_congr fun i => by rw [smul_pow, smul_smul]

set_option maxHeartbeats 200000 in
theorem aux_summable_smul (A : Mat ℝ n n) (t : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i) := by
  have h := expSeries_summable' (𝕂 := ℝ) (t • A)
  refine h.congr fun i => ?_
  rw [smul_pow, smul_smul]

set_option maxHeartbeats 400000 in
theorem IntervalMat.summable_expDiff (A : Mat ℝ n n) (t r : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial (i + 2) : ℝ))⁻¹
      * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 2)) := by
  have hst := aux_summable_smul A t
  have hsr : Summable (fun i : ℕ => (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i)) :=
    (aux_summable_smul A r).const_smul _
  have hg : Summable
      (fun i : ℕ => (((Nat.factorial i : ℝ))⁻¹ * (t ^ i - (t / r) * r ^ i)) • A ^ i) :=
    (hst.sub hsr).congr fun i => by simp only [smul_smul, ← sub_smul]; ring_nf
  exact (summable_nat_add_iff 2).mpr hg

set_option maxHeartbeats 400000 in
theorem IntervalMat.expDiff_eq_tsum (A : Mat ℝ n n) (t r : ℝ) (hr : r ≠ 0) :
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      = ∑' i : ℕ, (((Nat.factorial (i + 2) : ℝ))⁻¹
          * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 2) := by
  set g : ℕ → Mat ℝ n n :=
    fun i => (((Nat.factorial i : ℝ))⁻¹ * (t ^ i - (t / r) * r ^ i)) • A ^ i with hg
  have hst := aux_summable_smul A t
  have hsr : Summable (fun i : ℕ => (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i)) :=
    (aux_summable_smul A r).const_smul _
  have hcongr : ∀ i : ℕ,
      (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i
        - (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i) = g i := by
    intro i
    rw [hg]
    simp only [smul_smul, ← sub_smul]
    ring_nf
  have hgsum : Summable g := (hst.sub hsr).congr hcongr
  have htsum : ∑' i : ℕ, g i = exp (t • A) - (t / r) • exp (r • A) := by
    rw [aux_exp_smul_eq A t, aux_exp_smul_eq A r, ← tsum_const_smul'' (t / r),
      ← Summable.tsum_sub hst hsr]
    exact tsum_congr fun i => (hcongr i).symm
  have hshift := hgsum.sum_add_tsum_nat_add 2
  have hfirst : ∑ i ∈ Finset.range 2, g i = (1 - t / r) • (1 : Mat ℝ n n) := by
    have h1 : t - t / r * r = 0 := by rw [div_mul_cancel₀ t hr, sub_self]
    simp only [hg, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, h1, zero_smul,
      add_zero, mul_one]
  rw [← hshift, hfirst] at htsum
  have hrw : exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      = (exp (t • A) - (t / r) • exp (r • A)) - (1 - t / r) • (1 : Mat ℝ n n) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hrw, ← htsum]
  abel

end CORALean.Arithmetic.Real

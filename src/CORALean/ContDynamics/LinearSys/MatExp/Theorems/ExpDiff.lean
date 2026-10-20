module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul

@[expose] public section

/-!
# The interpolation error of a matrix exponential, as one series

`e^{At} - I - (t/r)(e^{Ar} - I)` is what the correction matrix has to cover: the gap between the
true flow and the straight line from `I` to `e^{Ar}`. Written here as a single series in `A^i`
starting at `i = 2`. The constant terms cancel against `I` and `(t/r)I`, and the linear terms
because `t - (t/r)r = 0`, which is why the correction is second order and why `r ≠ 0` is needed:
at `r = 0` Lean's `t/r` is `0`. Keeping the two exponentials in one series makes the `E(r)` bound
of [1, Prop. 3.1] provable: the tail terms share `A^i`, so `t^i - t·r^(i-1)` is bounded once
rather than each remainder separately and the two added. `CorrectionMatrix` spells out why
splitting them would cost a factor of two.

## Inputs
* `A` – system matrix
* `t` – time
* `r` – step length

## Hypotheses
* `hr` – step length nonzero

## Conclusion
* the interpolation error equals a series in powers starting at two

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

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_eq_tsum (A : Mat ℝ n n) (t r : ℝ) (hr : r ≠ 0) : -- --- CONCL ---
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      = ∑' i : ℕ, (((Nat.factorial (i + 2) : ℝ))⁻¹
          * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 2) := by -- --- PROOF ---
  set g : ℕ → Mat ℝ n n :=
    fun i => (((Nat.factorial i : ℝ))⁻¹ * (t ^ i - (t / r) * r ^ i)) • A ^ i with hg
  have hst := summable_exp_smul A t
  have hsr : Summable (fun i : ℕ => (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i)) :=
    (summable_exp_smul A r).const_smul _
  have hcongr : ∀ i : ℕ,
      (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i
        - (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i) = g i := by
    intro i
    rw [hg]
    simp only [smul_smul, ← sub_smul]
    ring_nf
  -- the two exponential series subtract termwise, which is what makes `g` a single series
  have hgsum : Summable g := (hst.sub hsr).congr hcongr
  have htsum : ∑' i : ℕ, g i = exp (t • A) - (t / r) • exp (r • A) := by
    rw [exp_smul_tsum A t, exp_smul_tsum A r, ← tsum_const_smul'' (t / r),
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

@[expose] public section

/-!
# The interpolation error of the integrated exponential, as one series

`∫₀ᵗ e^{Aσ}dσ - (t/r)∫₀ʳ e^{Aσ}dσ`, the error of [1, Sec. III-A]'s `F̃`, is the gap between the
integrated exponential and the straight line from `0` to its value at `r`. Written here as a single
series in `A^i`, starting at `A^1`: the `i = 0` term cancels because `t - (t/r) r = 0`, which is why
`r ≠ 0` is needed.

## Inputs
* `A` – system matrix
* `t` – time
* `r` – step length

## Hypotheses
* `hr` – step length nonzero

## Conclusion
* the interpolation error equals a series in powers starting at one

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       01-September-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interpolation error of the integrated exponential, as one series from
order `1` up. -/
theorem MatExp.expIntegralDiff_eq_tsum (A : Mat ℝ n n) (t r : ℝ)
    (hr : r ≠ 0) : -- --- CONCL ---
    MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r
      = ∑' i : ℕ, (((Nat.factorial (i + 2) : ℝ))⁻¹
          * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1) := by -- --- PROOF ---
  set g : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + 1) : ℝ))⁻¹ * (t ^ (i + 1) - (t / r) * r ^ (i + 1))) • A ^ i with hg
  have hst := MatExp.summable_expIntegral A t
  have hsr : Summable (fun i : ℕ =>
      (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i)) :=
    (MatExp.summable_expIntegral A r).const_smul _
  have hcongr : ∀ i : ℕ,
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i
        - (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i) = g i := by
    intro i
    rw [hg]
    simp only [smul_smul, ← sub_smul]
    ring_nf
  -- the two exponential series subtract termwise, which is all `hcongr` says
  have hgsum : Summable g := (hst.sub hsr).congr hcongr
  have htsum : ∑' i : ℕ, g i
      = MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r := by
    rw [MatExp.expIntegral, MatExp.expIntegral, ← tsum_const_smul'' (t / r),
      ← Summable.tsum_sub hst hsr]
    exact tsum_congr fun i => (hcongr i).symm
  have hshift := hgsum.sum_add_tsum_nat_add 1
  have hfirst : ∑ i ∈ Finset.range 1, g i = 0 := by
    have h1 : t - t / r * r = 0 := by rw [div_mul_cancel₀ t hr, sub_self]
    simp [hg, h1]
  rw [← htsum, ← hshift, hfirst, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

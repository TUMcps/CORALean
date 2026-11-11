module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral

@[expose] public section

/-!
# The series of the integrated exponential's interpolation error is summable

The series of `ExpIntegralDiffEqTsum`, `∑ᵢ (t^{i+2} - (t/r) r^{i+2})/(i+2)! · A^{i+1}`, is summable
[1, Sec. III-A]: the difference of the two exponential-integral series, shifted by one.

## Inputs
* `A` – system matrix
* `t` – time
* `r` – step length

## Hypotheses
* none

## Conclusion
* the series is summable

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

/-- The series of the interpolation error of the integrated exponential is summable. -/
theorem MatExp.summable_expIntegralDiff (A : Mat ℝ n n) (t r : ℝ) : -- --- CONCL ---
    Summable (fun i : ℕ => (((Nat.factorial (i + 2) : ℝ))⁻¹
      * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1)) := by -- --- PROOF ---
  have hst := MatExp.summable_expIntegral A t
  have hsr : Summable (fun i : ℕ =>
      (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i)) :=
    (MatExp.summable_expIntegral A r).const_smul _
  have hg : Summable (fun i : ℕ =>
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * (t ^ (i + 1) - (t / r) * r ^ (i + 1))) • A ^ i) :=
    (hst.sub hsr).congr fun i => by simp only [smul_smul, ← sub_smul]; ring_nf
  exact (summable_nat_add_iff (f := fun i : ℕ =>
    (((Nat.factorial (i + 1) : ℝ))⁻¹ * (t ^ (i + 1) - (t / r) * r ^ (i + 1))) • A ^ i) 1).mpr hg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

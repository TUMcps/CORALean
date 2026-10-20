module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul

@[expose] public section

/-!
# The interpolation-error series is summable, shifted past order two

Needed before `ExpDiff` can split its tsum into a finite sum and a tail: the
split lemma needs summability of the whole series, and shifting the index by
two is what drops the constant and linear terms that cancel.

## Inputs
* `A` – system matrix
* `t` – time
* `r` – step length

## Hypotheses
* none

## Conclusion
* the interpolation-error series is summable
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

theorem MatExp.summable_expDiff (A : Mat ℝ n n) (t r : ℝ) : -- --- CONCL ---
    Summable (fun i : ℕ => (((Nat.factorial (i + 2) : ℝ))⁻¹
      * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 2)) := by -- --- PROOF ---
  have hst := summable_exp_smul A t
  have hsr : Summable (fun i : ℕ => (t / r) • ((((Nat.factorial i : ℝ))⁻¹ * r ^ i) • A ^ i)) :=
    (summable_exp_smul A r).const_smul _
  have hg : Summable
      (fun i : ℕ => (((Nat.factorial i : ℝ))⁻¹ * (t ^ i - (t / r) * r ^ i)) • A ^ i) :=
    (hst.sub hsr).congr fun i => by simp only [smul_smul, ← sub_smul]; ring_nf
  exact (summable_nat_add_iff (f := fun i : ℕ =>
    (((Nat.factorial i : ℝ))⁻¹ * (t ^ i - (t / r) * r ^ i)) • A ^ i) 2).mpr hg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

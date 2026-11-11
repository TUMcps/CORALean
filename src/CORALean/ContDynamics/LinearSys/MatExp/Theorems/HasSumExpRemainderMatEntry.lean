module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq

@[expose] public section

/-!
# An entry of `E(Δt,η)` is the sum of its series

[1, Prop. 11], eq. (18): `E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!`, entry by entry, is the
sum of the exponential's series of `|A|Δt` from order `η + 1` on. The entrywise bounds on the
remainder of the exponential, of its interpolation error and of the integral's, compare their
terms with these.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order
* `j` – row index
* `k` – column index

## Hypotheses
* none

## Conclusion
* the series of the entries from order `η + 1` on has the sum `E(r,η)_{jk}`

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entries of the exponential series of `|A|r` from order `η + 1` on sum to `E(r,η)_{jk}`. -/
theorem MatExp.hasSum_expRemainderMat_entry (A : Mat ℝ n n) (r : ℝ) (η : ℕ)
    (j k : Fin n) : -- --- CONCL ---
    HasSum (fun i : ℕ => (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * r ^ (i + (η + 1)))
      • (MatExp.absMat A) ^ (i + (η + 1))) j k)
      (MatExp.expRemainderMat A r η j k) := by -- --- PROOF ---
  set B := MatExp.absMat A with hB
  set h : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹ * r ^ i) • B ^ i with hh
  have hsum : Summable h := summable_exp_smul B r
  have htay : MatExp.expTaylor (r • B) η = ∑ i ∈ Finset.range (η + 1), h i :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; simp only; rw [smul_pow, smul_smul]
  have hE : MatExp.expRemainderMat A r η = ∑' i, h (i + (η + 1)) := by
    rw [MatExp.expRemainderMat, ← hB, exp_smul_tsum B r, htay,
      ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  have hs : Summable fun i => h (i + (η + 1)) := (summable_nat_add_iff (η + 1)).mpr hsum
  have hc := (Matrix.entryLinearMap ℝ ℝ j k).continuous_of_finiteDimensional
  have hs' := hs.map (Matrix.entryLinearMap ℝ ℝ j k) hc
  rw [hE, MatExp.tsum_entry_eq hs j k]
  exact hs'.hasSum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

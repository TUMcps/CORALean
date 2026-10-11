import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq

/-!
# The exponential's Taylor remainder at `τ ∈ [0, Δt]` is entrywise under `E(Δt,η)`

[1, Prop. 11], eq. (18): `E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!` bounds the remainder of the
matrix exponential, which is what puts `(e^{Aτ} − Σ_{i≤η}(Aτ)ⁱ/i!) v` into `E(Δt,η)·v`'s interval
product for every `τ` up to `Δt`. Order by order, `|(Aⁱ)_{jk}| ≤ (|A|ⁱ)_{jk}` and `τⁱ ≤ Δtⁱ`; the
series are the exponential's from order `η + 1` on.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The remainder at `t • B`, entry `(j, k)`, as the exponential series from order `η + 1`. -/
theorem MatExp.aux_expRemainder_entry_eq (B : Mat ℝ n n) (t : ℝ) (η : ℕ) (j k : Fin n) :
    (exp (t • B) - MatExp.expTaylor (t • B) η) j k
      = ∑' i : ℕ, (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * t ^ (i + (η + 1)))
          • B ^ (i + (η + 1))) j k := by -- --- PROOF ---
  set h : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹ * t ^ i) • B ^ i with hh
  have hsum : Summable h := summable_exp_smul B t
  have htay : MatExp.expTaylor (t • B) η = ∑ i ∈ Finset.range (η + 1), h i :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; simp only; rw [smul_pow, smul_smul]
  have hE : exp (t • B) - MatExp.expTaylor (t • B) η = ∑' i, h (i + (η + 1)) := by
    rw [exp_smul_tsum B t, htay, ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  rw [hE, MatExp.tsum_entry_eq ((summable_nat_add_iff (η + 1)).mpr hsum) j k]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11], eq. (18): `|(e^{Aτ} − Σ_{i≤η}(Aτ)ⁱ/i!)_{jk}| ≤ E(Δt,η)_{jk}` for `0 ≤ τ ≤ Δt`. -/
theorem MatExp.abs_expRemainder_entry_le (A : Mat ℝ n n) {τ Δt : ℝ} (hτ : 0 ≤ τ)
    (hτΔt : τ ≤ Δt) (η : ℕ) (j k : Fin n) :
    |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k|
      ≤ (MatExp.expRemainderMat A Δt η) j k := by -- --- PROOF ---
  set B := MatExp.absMat A with hB
  have hΔt : 0 ≤ Δt := hτ.trans hτΔt
  -- the bounding series, entry `(j, k)` of `E(Δt,η)`, is summable
  have hEsum : Summable fun i : ℕ => (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹
      * Δt ^ (i + (η + 1))) • B ^ (i + (η + 1))) j k := by
    have h := (summable_nat_add_iff (η + 1)).mpr (summable_exp_smul B Δt)
    have hc := (Matrix.entryLinearMap ℝ ℝ j k).continuous_of_finiteDimensional
    exact (h.map (Matrix.entryLinearMap ℝ ℝ j k) hc)
  -- order by order: `|Aⁱ| ≤ |A|ⁱ` and `τⁱ ≤ Δtⁱ`
  have hdom : ∀ i : ℕ, |((((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * τ ^ (i + (η + 1)))
      • A ^ (i + (η + 1))) j k)|
      ≤ (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
        • B ^ (i + (η + 1))) j k := fun i => by
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
    have hf : (0:ℝ) ≤ (Nat.factorial (i + (η + 1)) : ℝ)⁻¹ := by positivity
    rw [abs_of_nonneg hf, abs_of_nonneg (pow_nonneg hτ _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ hτΔt _) hf)
      (abs_pow_entry_le_absMat_pow_entry A _ j k) (abs_nonneg _)
      (mul_nonneg hf (pow_nonneg hΔt _))
  -- so the remainder's entries are absolutely summable, and dominated term by term
  have hPsum := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hdom hEsum
  rw [MatExp.aux_expRemainder_entry_eq A τ η j k, MatExp.expRemainderMat, ← hB,
    MatExp.aux_expRemainder_entry_eq B Δt η j k]
  calc |∑' i, ((((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * τ ^ (i + (η + 1)))
          • A ^ (i + (η + 1))) j k)|
      ≤ ∑' i, |((((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * τ ^ (i + (η + 1)))
          • A ^ (i + (η + 1))) j k)| := by
        have h := norm_tsum_le_tsum_norm (f := fun i => ((((Nat.factorial (i + (η + 1)) : ℝ)⁻¹
          * τ ^ (i + (η + 1))) • A ^ (i + (η + 1))) j k)) (by
            simpa only [Real.norm_eq_abs] using hPsum)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ _ := hPsum.tsum_le_tsum hdom hEsum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

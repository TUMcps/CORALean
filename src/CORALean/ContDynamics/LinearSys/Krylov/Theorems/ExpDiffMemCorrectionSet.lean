module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.CorrectionSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq

@[expose] public section

/-!
# The interpolation error of the reduced exponential lies in the correction set

[1, Lemma III.3], at the matrix: for `t ∈ [0, δ]`, `e^{Ht} - I - (t/δ)(e^{Hδ} - I) ∈ F`. The
error is `Σ_{i≥2} (tⁱ - tδ^{i-1}) Hⁱ/i!`; orders `2…η` keep `tⁱ - tδ^{i-1}`, which lies in
`[corrCoeff i · δⁱ, 0]`, and the tail past `η` is bounded entrywise term by term,
`|tⁱ - tδ^{i-1}| ≤ δⁱ` and `|Hⁱ| ≤ |H|ⁱ`, by `W(δ)`. As [1]'s proof does it: one series, not two
remainders each bounded on their own (which would give `2W(δ)`).

## Inputs
* `H` – Hessenberg matrix
* `δ` – step length
* `η` – Taylor order
* `t` – time

## Hypotheses
* `hδ` – step length positive
* `hη` – order at least one
* `ht0` – time nonnegative
* `htδ` – time at most the step length

## Conclusion
* the interpolation error of the exponential lies in the correction set

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov
      Subspace". IEEE Transactions on Automatic Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One order's scalar factor: `|tᵏ - (t/δ)δᵏ| ≤ δᵏ` on `[0, δ]`. -/
private theorem Krylov.aux_abs_coeff_le {δ t : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (htδ : t ≤ δ)
    (k : ℕ) : -- --- CONCL ---
    |t ^ k - (t / δ) * δ ^ k| ≤ δ ^ k := by -- --- PROOF ---
  have h1 : 0 ≤ t ^ k := pow_nonneg ht0 k
  have h2 : t ^ k ≤ δ ^ k := pow_le_pow_left₀ ht0 htδ k
  have h3 : 0 ≤ (t / δ) * δ ^ k := mul_nonneg (div_nonneg ht0 hδ.le) (pow_nonneg hδ.le k)
  have h4 : (t / δ) * δ ^ k ≤ δ ^ k :=
    mul_le_of_le_one_left (pow_nonneg hδ.le k) ((div_le_one hδ).mpr htδ)
  exact abs_sub_le_of_nonneg_of_le h1 h2 h3 h4

/-- `i = 2, …, η` is `2 + i` over `i < η - 1`. -/
private theorem Krylov.aux_sum_Icc_two {M : Type} [AddCommMonoid M] (η : ℕ) (hη : 1 ≤ η)
    (g : ℕ → M) :
    ∑ i ∈ Finset.Icc 2 η, g i = ∑ i ∈ Finset.range (η - 1), g (i + 2) := by
  have h : Finset.Icc 2 η = Finset.Ico 2 (η - 1 + 2) := by
    ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sum_range, show η - 1 + 2 - 2 = η - 1 by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.expDiff_mem_correctionSet (H : Mat ℝ m m) {δ : ℝ} (hδ : 0 < δ) {η : ℕ}
    (hη : 1 ≤ η) {t : ℝ} (ht0 : 0 ≤ t) (htδ : t ≤ δ) : -- --- CONCL ---
    exp (t • H) - 1 - (t / δ) • (exp (δ • H) - 1)
      ∈ Krylov.correctionSet H δ η := by -- --- PROOF ---
  set f : ℕ → Mat ℝ m m := fun i => (((Nat.factorial (i + 2) : ℝ))⁻¹
    * (t ^ (i + 2) - (t / δ) * δ ^ (i + 2))) • H ^ (i + 2) with hf
  have hsum : Summable f := MatExp.summable_expDiff H t δ
  have hsplit := hsum.sum_add_tsum_nat_add (η - 1)
  set E := ∑' i, f (i + (η - 1)) with hE
  refine ⟨fun k => t ^ k - (t / δ) * δ ^ k, E, fun k hk => ?_, fun j k => ?_, ?_⟩
  · -- orders `2…η`: the coefficient lies in its interval
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    set s := t / δ with hs
    have hs0 : 0 ≤ s := div_nonneg ht0 hδ.le
    have hs1 : s ≤ 1 := (div_le_one hδ).mpr htδ
    have ht : t = s * δ := by rw [hs, div_mul_cancel₀ _ hδ.ne']
    have hrw : t ^ k - s * δ ^ k = δ ^ k * (s ^ k - s) := by
      rw [ht, mul_pow]; ring
    show t ^ k - s * δ ^ k ∈ _
    rw [hrw]
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hδ.le k)
      (sub_nonpos.mpr (pow_le_of_le_one hs0 hs1 (by omega)))⟩
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (MatExp.corrCoeff_le_sub hk2 hs0) (pow_nonneg hδ.le k)
  · -- the tail, one entry at a time, against the exponential series at `|H|`
    have hW := MatExp.hasSum_expRemainderMat_entry H δ η j k
    have hsE : Summable (fun i => f (i + (η - 1))) := (summable_nat_add_iff _).mpr hsum
    have hterm : ∀ i, |(f (i + (η - 1))) j k| ≤ ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹
        * δ ^ (i + (η + 1))) * ((MatExp.absMat H) ^ (i + (η + 1))) j k := by
      intro i
      have he : i + (η - 1) + 2 = i + (η + 1) := by omega
      simp only [hf, Matrix.smul_apply, smul_eq_mul, he]
      rw [abs_mul, abs_mul, abs_inv, Nat.abs_cast, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (Krylov.aux_abs_coeff_le hδ ht0 htδ _)
        (abs_pow_entry_le_absMat_pow_entry H _ j k) (abs_nonneg _) (pow_nonneg hδ.le _))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    have habs : Summable (fun i => |(f (i + (η - 1))) j k|) :=
      Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm hW.summable
    show |E j k| ≤ _
    rw [hE, MatExp.tsum_entry_eq hsE j k, ← hW.tsum_eq]
    have hnorm := norm_tsum_le_tsum_norm (f := fun i => (f (i + (η - 1))) j k)
      (by simpa only [Real.norm_eq_abs] using habs)
    simp only [Real.norm_eq_abs] at hnorm
    exact hnorm.trans (Summable.tsum_le_tsum hterm habs hW.summable)
  · -- the finite orders, reindexed from `i + 2`
    rw [MatExp.expDiff_eq_tsum H t δ hδ.ne', ← hsplit, Krylov.aux_sum_Icc_two η hη]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf, smul_smul]
    ring_nf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

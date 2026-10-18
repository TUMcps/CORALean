module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq

@[expose] public section

/-!
# `Σ_{i>η} Ãᵢ` is entrywise under `E(Δt,η)·Δt`

The step [1, `Prop. 11`]'s display `(18)` takes without proof, and [2, Eq. 7]'s `Ẽ(t) =
Ê(t)t`: `expIntegral`'s own *infinite* tail past the truncation order is dominated, entry
for entry, by the *finite* `E(Δt,η)Δt` eq. (20)'s remainder block carries. The two series
are different — `Aⁱ Δtⁱ⁺¹/(i+1)!` against `(|A|Δt)ⁱ/i!` scaled by `Δt` — but they match
power for power once `abs_pow_entry_le_absMat_pow_entry` replaces `Aⁱ` by `|A|ⁱ`, and
`(i+1)! ≥ i!` finishes each term. No `Δt ≤ 1` is needed: the two `Δt`-powers are already
equal, `Δt · Δtⁱ = Δtⁱ⁺¹`.

`MatExp.tsum_entry_eq` reads both sides one entry at a time, `aux_summable_entry`
being the summability that goes with it.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Evaluating a matrix at one entry, as an additive homomorphism. -/
def aux_entryHom (j k : Fin n) : Mat ℝ n n →+ ℝ where
  toFun M := M j k
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reading one entry is `1`-Lipschitz, hence continuous, so it carries summability across — the
companion of `MatExp.tsum_entry_eq`, which needs the sum to exist. -/
theorem aux_summable_entry {f : ℕ → Mat ℝ n n} (hf : Summable f) (j k : Fin n) :
    Summable (fun i => (f i) j k) := by -- --- PROOF ---
  have hlip : LipschitzWith 1 (aux_entryHom (n := n) j k) := by
    refine LipschitzWith.of_dist_le_mul fun M N => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    simpa only [aux_entryHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.sub_apply] using
      abs_entry_le_norm (M - N) j k
  exact hf.map (aux_entryHom j k) hlip.continuous

/-- `|∑' p| ≤ ∑' |p|` for a real series, away from any matrix instance. -/
theorem aux_abs_tsum_le_tsum_abs {p : ℕ → ℝ} (hp : Summable fun i => |p i|) :
    |∑' i, p i| ≤ ∑' i, |p i| := by
  have h := norm_tsum_le_tsum_norm (f := p) (by simpa only [Real.norm_eq_abs] using hp)
  simpa only [Real.norm_eq_abs] using h

/-- `E(Δt,η)`'s entry is the exponential series at `|A|` from order `η+1` on. -/
theorem aux_expRemainderMat_entry_eq (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) (j k : Fin n) :
    (MatExp.expRemainderMat A Δt η) j k
      = ∑' i : ℕ, ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k := by -- --- PROOF ---
  set B := MatExp.absMat A with hB
  set h : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹ * Δt ^ i) • B ^ i with hh
  have hsum : Summable h := summable_exp_smul B Δt
  have htay : MatExp.expTaylor (Δt • B) η = ∑ i ∈ Finset.range (η + 1), h i :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; simp only; rw [smul_pow, smul_smul]
  have hE : MatExp.expRemainderMat A Δt η = ∑' i, h (i + (η + 1)) := by
    rw [MatExp.expRemainderMat, ← hB, exp_smul_tsum B Δt, htay, ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  rw [hE, MatExp.tsum_entry_eq ((summable_nat_add_iff (f := h) (η + 1)).mpr hsum) j k]
  exact tsum_congr fun i => rfl

/-- `expIntegral`'s tail past order `η`, likewise read off one entry at a time. -/
theorem aux_particularTail_entry_eq (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) (j k : Fin n) :
    (MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i) j k
      = ∑' i : ℕ, (MatExp.particularCoeff A Δt (i + (η + 1))) j k := by -- --- PROOF ---
  have hsum : Summable (fun i => MatExp.particularCoeff A Δt i) :=
    (MatExp.summable_expIntegral A Δt).congr fun i => by
      simp only [MatExp.particularCoeff, div_eq_inv_mul]
  have hEI : MatExp.expIntegral A Δt = ∑' i, MatExp.particularCoeff A Δt i :=
    tsum_congr fun i => by simp only [MatExp.particularCoeff, div_eq_inv_mul]
  have hT : MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i
      = ∑' i, MatExp.particularCoeff A Δt (i + (η + 1)) := by
    rw [hEI, ← hsum.sum_add_tsum_nat_add (η + 1)]; abel
  rw [hT, MatExp.tsum_entry_eq
    ((summable_nat_add_iff (f := fun i => MatExp.particularCoeff A Δt i) (η + 1)).mpr hsum) j k]

/-- One order of the tail, against the same order of `E(Δt,η)·Δt`. -/
theorem aux_abs_particularCoeff_entry_le (A : Mat ℝ n n) {Δt : ℝ} (hΔt : 0 ≤ Δt) (m : ℕ)
    (j k : Fin n) : -- --- STMT ---
    |(MatExp.particularCoeff A Δt m) j k|
      ≤ Δt * (((Nat.factorial m : ℝ)⁻¹ * Δt ^ m)
        * ((MatExp.absMat A) ^ m) j k) := by -- --- PROOF ---
  have hpow : (MatExp.particularCoeff A Δt m) j k
      = Δt ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) * (A ^ m) j k := rfl
  have hfac : (0:ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfac1 : (Nat.factorial m : ℝ) ≤ (Nat.factorial (m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ m)
  have hscal : Δt ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) ≤ Δt * ((Nat.factorial m : ℝ)⁻¹ * Δt ^ m)
      := by
    rw [inv_mul_eq_div, mul_div_assoc', ← pow_succ']
    exact div_le_div_of_nonneg_left (pow_nonneg hΔt _) hfac hfac1
  have hentry : |(A ^ m) j k| ≤ ((MatExp.absMat A) ^ m) j k :=
    abs_pow_entry_le_absMat_pow_entry A m j k
  rw [hpow, abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg hΔt _) (Nat.cast_nonneg _))]
  calc Δt ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) * |(A ^ m) j k|
      ≤ Δt ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) * ((MatExp.absMat A) ^ m) j k :=
        mul_le_mul_of_nonneg_left hentry (div_nonneg (pow_nonneg hΔt _) (Nat.cast_nonneg _))
    _ ≤ Δt * ((Nat.factorial m : ℝ)⁻¹ * Δt ^ m) * ((MatExp.absMat A) ^ m) j k :=
        mul_le_mul_of_nonneg_right hscal ((abs_nonneg _).trans hentry)
    _ = Δt * (((Nat.factorial m : ℝ)⁻¹ * Δt ^ m) * ((MatExp.absMat A) ^ m) j k) := by ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s step `(18)`: `expIntegral`'s tail past order `η` is entrywise under `E(Δt,η)·Δt`. -/
theorem MatExp.abs_particularTail_entry_le (A : Mat ℝ n n) {Δt : ℝ} (hΔt : 0 ≤ Δt) (η : ℕ)
    (j k : Fin n) :
    |(MatExp.expIntegral A Δt - ∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i) j k|
      ≤ Δt * (MatExp.expRemainderMat A Δt η) j k := by -- --- PROOF ---
  have hEsum : Summable fun i : ℕ => ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
      * ((MatExp.absMat A) ^ (i + (η + 1))) j k :=
    aux_summable_entry (f := fun i => ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹
      * Δt ^ (i + (η + 1))) • (MatExp.absMat A) ^ (i + (η + 1)))
      ((summable_nat_add_iff (f := fun i : ℕ => ((Nat.factorial i : ℝ)⁻¹ * Δt ^ i)
        • (MatExp.absMat A) ^ i) (η + 1)).mpr (summable_exp_smul (MatExp.absMat A) Δt)) j k
  have hdom : ∀ i : ℕ, |(MatExp.particularCoeff A Δt (i + (η + 1))) j k|
      ≤ Δt * (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
        * ((MatExp.absMat A) ^ (i + (η + 1))) j k) := fun i =>
    aux_abs_particularCoeff_entry_le A hΔt (i + (η + 1)) j k
  have hPsum : Summable fun i : ℕ => |(MatExp.particularCoeff A Δt (i + (η + 1))) j k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hdom (hEsum.mul_left Δt)
  -- the entry of the tail, then term by term against `Δt · E`, then the scalar out of the sum
  rw [aux_particularTail_entry_eq A Δt η j k, aux_expRemainderMat_entry_eq A Δt η j k]
  calc |∑' i, (MatExp.particularCoeff A Δt (i + (η + 1))) j k|
      ≤ ∑' i, |(MatExp.particularCoeff A Δt (i + (η + 1))) j k| := aux_abs_tsum_le_tsum_abs hPsum
    _ ≤ ∑' i, Δt * (((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k) :=
        hPsum.tsum_le_tsum hdom (hEsum.mul_left Δt)
    _ = Δt * ∑' i, ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
          * ((MatExp.absMat A) ^ (i + (η + 1))) j k := tsum_mul_left

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

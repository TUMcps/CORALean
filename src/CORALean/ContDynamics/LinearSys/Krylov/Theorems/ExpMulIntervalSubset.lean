module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumMatrixEntryEq
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The exponential of an interval vector in the Krylov subspace

[1, Lemma III.2]: for `[b̲, b̄] = b_c ⊕ [-b_Δ, b_Δ]`, `e^{At}[b̲, b̄] ⊆ x̂(b_c) ⊕ [-μ, μ]`,
`μ = x̄(b_Δ) + 1ₙ(‖b_Δ‖ε̄ t + ‖b_c‖ε t)`, where `x̂(b_c)` approximates `e^{At}b_c` and `x̄(b_Δ)`
approximates `e^{|A|t}b_Δ`, each within its a-posteriori bound (3) — the hypotheses here.
The step [1] takes from the Taylor series, `|e^{At}| ≤ e^{|A|t}` entrywise for `t ≥ 0`, is
proved: `|Aⁱ| ≤ |A|ⁱ` term by term.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
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

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Reading one entry, as an additive homomorphism. -/
def Krylov.aux_entryHom (j k : Fin n) : Mat ℝ n n →+ ℝ where
  toFun M := M j k
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reading one entry carries summability across. -/
theorem Krylov.aux_summable_entry {f : ℕ → Mat ℝ n n} (hf : Summable f) (j k : Fin n) :
    Summable (fun i => (f i) j k) := by -- --- PROOF ---
  have hlip : LipschitzWith 1 (Krylov.aux_entryHom (n := n) j k) := by
    refine LipschitzWith.of_dist_le_mul fun M N => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    simpa only [Krylov.aux_entryHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.sub_apply] using
      abs_entry_le_norm (M - N) j k
  exact hf.map (Krylov.aux_entryHom j k) hlip.continuous

/-- `|e^{At}| ≤ e^{|A|t}` entrywise, for `t ≥ 0`. -/
theorem Krylov.aux_abs_exp_entry_le (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t) (j k : Fin n) :
    |(exp (t • A)) j k| ≤ (exp (t • MatExp.absMat A)) j k := by -- --- PROOF ---
  have hsA := summable_exp_smul A t
  have hsB := summable_exp_smul (MatExp.absMat A) t
  rw [exp_smul_tsum A t, exp_smul_tsum (MatExp.absMat A) t, MatExp.tsum_entry_eq hsA j k,
    MatExp.tsum_entry_eq hsB j k]
  have hcoef : ∀ i : ℕ, 0 ≤ (Nat.factorial i : ℝ)⁻¹ * t ^ i :=
    fun i => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg ht i)
  have hterm : ∀ i : ℕ, |((((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i) j k|
      ≤ ((((Nat.factorial i : ℝ))⁻¹ * t ^ i) • MatExp.absMat A ^ i) j k := by
    intro i
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hcoef i)]
    exact mul_le_mul_of_nonneg_left (abs_pow_entry_le_absMat_pow_entry A i j k) (hcoef i)
  have hB := Krylov.aux_summable_entry hsB j k
  have habs : Summable (fun i => |((((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i) j k|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hB
  have hnorm := norm_tsum_le_tsum_norm
    (f := fun i => ((((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i) j k)
    (by simpa only [Real.norm_eq_abs] using habs)
  simp only [Real.norm_eq_abs] at hnorm
  exact hnorm.trans (Summable.tsum_le_tsum hterm habs hB)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.exp_mul_interval_subset (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t) (bc bΔ : Vec ℝ n)
    (xhat xbar : Vec ℝ n) {ε εbar : ℝ}
    (hc : ‖exp (t • A) *ᵥ bc - xhat‖₂ ≤ ‖bc‖₂ * ε * t)
    (hΔ : ‖exp (t • MatExp.absMat A) *ᵥ bΔ - xbar‖₂ ≤ ‖bΔ‖₂ * εbar * t)
    {x : Vec ℝ n} (hx : ∀ j, |x j - bc j| ≤ bΔ j) (j : Fin n) : -- --- STMT ---
    |(exp (t • A) *ᵥ x - xhat) j|
      ≤ xbar j + (‖bΔ‖₂ * εbar * t + ‖bc‖₂ * ε * t) := by -- --- PROOF ---
  -- the center's error, and `e^{At}` applied to the deviation `x - b_c`
  have hsplit : exp (t • A) *ᵥ x - xhat
      = (exp (t • A) *ᵥ bc - xhat) + exp (t • A) *ᵥ (x - bc) := by
    rw [mulVec_sub]; abel
  have h1 : |(exp (t • A) *ᵥ bc - xhat) j| ≤ ‖bc‖₂ * ε * t := (abs_le_norm₂ _ j).trans hc
  have h2 : |(exp (t • A) *ᵥ (x - bc)) j| ≤ (exp (t • MatExp.absMat A) *ᵥ bΔ) j := by
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (Krylov.aux_abs_exp_entry_le A ht j k) (by simpa using hx k)
      (abs_nonneg _) ((abs_nonneg _).trans (Krylov.aux_abs_exp_entry_le A ht j k))
  have h3 : (exp (t • MatExp.absMat A) *ᵥ bΔ) j ≤ xbar j + ‖bΔ‖₂ * εbar * t := by
    have := (abs_le_norm₂ _ j).trans hΔ
    rw [Pi.sub_apply] at this
    linarith [le_abs_self ((exp (t • MatExp.absMat A) *ᵥ bΔ) j - xbar j)]
  rw [hsplit, Pi.add_apply]
  linarith [abs_add_le ((exp (t • A) *ᵥ bc - xhat) j) ((exp (t • A) *ᵥ (x - bc)) j)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

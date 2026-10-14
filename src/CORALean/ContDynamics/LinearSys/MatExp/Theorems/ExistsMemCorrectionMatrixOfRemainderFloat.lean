module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulVecEqOfNormLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RescaledPeanoBakerTermMemMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPowSubset
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Interval.Real.Theorems.AbsMaxSmul
public import CORALean.ContSet.Interval.Real.Theorems.ExistsNormEqAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# The truncated Peano–Baker series plus a short remainder, over a float box

`Real.MatExp.exists_mem_intervalCorrectionMatrix_of_remainder` with the float
step's own two interval matrices, `expIntervalEnclosure (r • A)` and
`intervalCorrectionMatrix A r` at a float box `A`, every `Â(σ)` in it. Their
float guarantees are stated per member's exponential, and a Peano–Baker term is
no member's, so this goes through the boxes themselves: the `k`-th rescaled term
lies in the real `k`-th power of `r • A`'s nominal box, and that is inside the
float power (`Interval.matPow_subset`), the box admitting products of different
members in both layers; likewise the unscaled power the correction term scales.
From there the coefficients `1/k!` and `(λ^k - λ) r^k/k!` lie in the float
intervals `invFactorialBounds` and `[cLo, 0]`, and the remainder `ρ` is a matrix
within the float remainder bound, which bounds the real one at a member attaining
the box's norm.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix MeasureTheory NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A positive scaling of a non-empty nominal box sits inside the float scaling. -/
theorem aux_smul_subset (A : Interval (Mat 𝕋 n n)) {r : 𝕋} (hr : 0 < toReal r)
    {M₀ : Mat ℝ n n} (hM₀ : M₀ ∈ A.construct) :
    (Real.Interval.smul (toReal r) A.nominal).construct
      ⊆ (Interval.smul r r A).construct := by -- --- PROOF ---
  intro P hP
  have hw : ∀ i j, A.nominal.inf i j ≤ A.nominal.sup i j := fun i j =>
    (Real.Interval.mem_mat_iff.mp hM₀ i j).1.trans (Real.Interval.mem_mat_iff.mp hM₀ i j).2
  -- the point is `r` times a point of the box
  have hmem : (toReal r)⁻¹ • P ∈ A.construct := by
    refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
    have h := Real.Interval.mem_mat_iff.mp hP i j
    simp only [Real.Interval.smul, Entrywise.ofEntry, Entrywise.entry] at h
    rw [min_eq_left (mul_le_mul_of_nonneg_left (hw i j) hr.le),
      max_eq_right (mul_le_mul_of_nonneg_left (hw i j) hr.le)] at h
    simp only [Matrix.smul_apply, smul_eq_mul]
    constructor
    · rw [le_inv_mul_iff₀ hr]; exact h.1
    · rw [inv_mul_le_iff₀ hr]; exact h.2
  have h := Interval.smul_outer (cLo := r) (cHi := r) le_rfl le_rfl A hmem
  rwa [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first `η + 1` Peano–Baker terms of a matrix in the float box `A`, applied to
`x₀` and widened by a short `ρ`, are the interpolation to a member of the float
exponential enclosure plus a member of the float correction matrix applied to `x₀`. -/
theorem MatExp.exists_mem_intervalCorrectionMatrix_of_remainder (A : Interval (Mat 𝕋 n n))
    {Â : ℝ → Mat ℝ n n} (hÂ : ∀ i j a b, IntervalIntegrable (fun s => Â s i j) volume a b)
    (hÂB : ∀ s, Â s ∈ A.construct) {r : 𝕋} (hr : 0 < toReal r) {m : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / (((m + 2 : ℕ) : ℝ) + 2)
      ≤ 1 / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) (x₀ ρ : Vec ℝ n)
    (hρ : ‖ρ‖ ≤ ‖x₀‖ * Real.MatExp.expRemainderBound
      (Real.Interval.smul t A.nominal).absMax (m + 2)) :
    ∃ Φ ∈ (MatExp.expIntervalEnclosure (Interval.smul r r A) (m + 2)).construct,
      ∃ F ∈ (MatExp.intervalCorrectionMatrix A r (m + 2)).construct,
        ∑ k ∈ Finset.range (m + 2 + 1), Real.MatExp.peanoBakerTerm Â k t *ᵥ x₀ + ρ
          = ((1 - t / toReal r) • x₀ + (t / toReal r) • (Φ *ᵥ x₀)) + F *ᵥ x₀ := by -- --- PROOF ---
  set η := m + 2 with hη
  set rr := toReal r with hrr
  set nrm := MatExp.normUpperBound (Interval.smul r r A) with hnrm
  have hÂB' : ∀ s, Â s ∈ A.nominal.construct := hÂB
  -- a member as long as the box, and the float remainder bound above the real one
  obtain ⟨M, hM, hMn⟩ := Real.Interval.exists_norm_eq_absMax (hÂB 0)
  have hrM : ‖rr • M‖ ≤ toReal nrm := MatExp.norm_smul_le_normUpperBound A r hM
  have hnn : 0 ≤ toReal nrm := (norm_nonneg _).trans hrM
  -- the condition at the member, then the real bound at `t` under the one at `r • M`
  have hden : (0:ℝ) < (η : ℝ) + 2 := by positivity
  have hεM : ‖rr • M‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hrM hden.le) hε) (by norm_num)
  have hRf := MatExp.expRemainderBound_le η hrM hnn hε
  have htabs : ‖(Real.Interval.smul t A.nominal).absMax‖ ≤ ‖rr • M‖ := by
    rw [Real.Interval.absMax_smul _ ht0, norm_smul, norm_smul, Real.norm_of_nonneg ht0,
      Real.norm_of_nonneg hr.le, hMn]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hRt := Real.MatExp.expRemainderBound_mono η htabs hεM
  -- `ρ` a matrix within the float bound, applied to `x₀`
  set R := toReal (MatExp.expRemainderBound nrm η) with hR
  have hR0 : 0 ≤ R := by
    refine le_trans ?_ hRf
    have h1 : 0 < 1 - ‖rr • M‖ / ((η : ℝ) + 2) := by linarith
    rw [Real.MatExp.expRemainderBound]; positivity
  obtain ⟨E, hE, hEv⟩ := Real.exists_mulVec_eq_of_norm_le hR0
    (hρ.trans (mul_le_mul_of_nonneg_left (hRt.trans hRf) (norm_nonneg _)))
  -- the correction's kept orders, entrywise between zero and the stored terms, plus `E`
  have hFE : ∀ Cf : ℕ → Mat ℝ n n, (∀ i j k,
      min (toReal ((MatExp.intervalCorrTerm A r (i + 2)).inf j k)) 0 ≤ Cf i j k ∧
        Cf i j k ≤ max (toReal ((MatExp.intervalCorrTerm A r (i + 2)).sup j k)) 0) →
      ∑ i ∈ Finset.range (η - 1), Cf i + E
        ∈ (MatExp.intervalCorrectionMatrix A r η).construct := by
    intro Cf hCf
    refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
    -- each rounded sum brackets the exact one, term by term
    have hlo : toReal (sumDown fun i : Fin (η - 1) =>
          minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero)
        ≤ ∑ i ∈ Finset.range (η - 1), Cf i j k := by
      refine le_trans (sumDown_le_sum _) ?_
      rw [← Fin.sum_univ_eq_sum_range (fun i => Cf i j k)]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [toReal_minimum, toReal_zero]
      exact (hCf i j k).1
    have hhi : ∑ i ∈ Finset.range (η - 1), Cf i j k
        ≤ toReal (sumUp fun i : Fin (η - 1) =>
          maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero) := by
      refine le_trans ?_ (sum_le_sumUp _)
      rw [← Fin.sum_univ_eq_sum_range (fun i => Cf i j k)]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [toReal_maximum, toReal_zero]
      exact (hCf i j k).2
    -- and the stored entry is their rounded difference and sum with the bound
    have hEjk := abs_le.mp (hE j k)
    set sLo := sumDown fun i : Fin (η - 1) =>
      minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero
    set sHi := sumUp fun i : Fin (η - 1) =>
      maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero
    simp only [MatExp.intervalCorrectionMatrix, Interval.materialiseMat_eq, Interval.nominal,
      RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
    show toReal (subDown sLo _) ≤ _ ∧ _ ≤ toReal (addUp sHi _)
    have hsd := subDown_le_sub sLo (MatExp.expRemainderBound nrm η)
    have hau := add_le_addUp sHi (MatExp.expRemainderBound nrm η)
    rw [Matrix.add_apply, Matrix.sum_apply]
    exact ⟨by linarith [hEjk.1], by linarith [hEjk.2]⟩
  rcases ht0.eq_or_lt with rfl | ht
  · -- at the start of the step the terms are the identity, and the widening is all of `F`
    refine ⟨exp (rr • Â 0), MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer le_rfl le_rfl A (hÂB 0)) hε, ∑ i ∈ Finset.range (η - 1), 0 + E,
      hFE (fun _ => 0) fun i j k => ⟨min_le_right _ 0, le_max_right _ 0⟩, ?_⟩
    have hz : (Matrix.of fun _ _ => (0:ℝ) : Mat ℝ n n) = 0 := rfl
    rw [Finset.sum_const_zero, zero_add, hEv, Finset.sum_range_succ']
    simp [Real.MatExp.peanoBakerTerm, hz]
  set lam := t / rr with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht.le hr.le
  have hlam1 : lam ≤ 1 := (div_le_one hr).mpr htr
  set Q : ℕ → Mat ℝ n n := fun k => (rr / t) ^ k • Real.MatExp.peanoBakerTerm Â k t with hQ
  have hQreal : ∀ k, (Nat.factorial k : ℝ) • Q k
      ∈ (Real.Interval.matPow (Real.Interval.smul rr A.nominal) k).construct := fun k =>
    Real.MatExp.rescaled_peanoBakerTerm_mem_matPow hÂ hÂB' k ht hr.le
  -- each order in the float power of `r • A`, and unscaled in the float power of `A`
  have hQmem : ∀ k, (Nat.factorial k : ℝ) • Q k
      ∈ (Interval.matPow (Interval.smul r r A) k).construct := fun k =>
    Interval.matPow_subset (Real.Interval.smul_outer rr _ (hÂB' 0))
      (aux_smul_subset A hr (hÂB 0)) k (hQreal k)
  have hNmem : ∀ k, (rr ^ k)⁻¹ • ((Nat.factorial k : ℝ) • Q k)
      ∈ (Interval.matPow A k).construct := fun k => by
    refine Interval.matPow_subset (hÂB' 0) subset_rfl k ?_
    -- dividing by `r^k` undoes the scaling of the box
    have hsc := Real.Interval.matPow_smul A.nominal hr.le k
    have hm := Real.Interval.mem_mat_iff.mp (hQreal k)
    rw [hsc.1, hsc.2] at hm
    have hp : 0 < rr ^ k := by positivity
    refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
    obtain ⟨h1, h2⟩ := hm i j
    simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
    constructor
    · rw [le_inv_mul_iff₀ hp]; exact h1
    · rw [inv_mul_le_iff₀ hp]; exact h2
  have hPQ : ∀ k, Real.MatExp.peanoBakerTerm Â k t = lam ^ k • Q k := fun k => by
    simp only [hQ, hlam, smul_smul, ← mul_pow,
      div_mul_div_comm, mul_comm t rr, div_self (mul_ne_zero hr.ne' ht.ne'), one_pow, one_smul]
  -- the mapping matrix: the rescaled terms, each in its order of the float Taylor box
  have hΦ : ∑ k ∈ Finset.range (η + 1), Q k
      ∈ (MatExp.expIntervalEnclosure (Interval.smul r r A) η).construct := by
    have hterm : ∀ k, Q k ∈ (Interval.smul (MatExp.invFactorialBounds k).inf
        (MatExp.invFactorialBounds k).sup
        (Interval.matPow (Interval.smul r r A) k)).construct := fun k => by
      have h := Interval.smul_outer (MatExp.invFactorialBounds_mem k).1
        (MatExp.invFactorialBounds_mem k).2 _ (hQmem k)
      rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h
    -- summed as the float Taylor box recurses, then widened by the bound
    have htay : ∀ η', ∑ k ∈ Finset.range (η' + 1), Q k
        ∈ (MatExp.expIntervalTaylor (Interval.smul r r A) η').construct := by
      intro η'
      induction η' with
      | zero => rw [Finset.sum_range_one]; exact hterm 0
      | succ k ih =>
        show _ ∈ (Interval.matPlus _ _).materialiseMat.construct
        rw [Interval.materialiseMat_eq]
        have h := Interval.matPlus_outer _ _ (hterm (k + 1)) ih
        rw [add_comm (Q (k + 1)), ← Finset.sum_range_succ] at h
        exact h
    refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
    have h := Real.Interval.mem_mat_iff.mp (htay η) i j
    simp only [Interval.nominal, RealImage.realImage, toRealMat] at h
    show toReal (subDown _ _) ≤ _ ∧ _ ≤ toReal (addUp _ _)
    have hsd := subDown_le_sub ((MatExp.expIntervalTaylor (Interval.smul r r A) η).inf i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η)
    have hau := add_le_addUp ((MatExp.expIntervalTaylor (Interval.smul r r A) η).sup i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η)
    constructor <;> linarith [h.1, h.2]
  -- the correction: orders `2 … η`, each weighted by `λ^k - λ`, inside the stored term
  set Cf : ℕ → Mat ℝ n n := fun i => (lam ^ (i + 2) - lam) • Q (i + 2) with hCf
  have hF := hFE Cf fun i j k => by
    have hi : 2 ≤ i + 2 := by omega
    obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr.le (i + 2)
    set ρk := rr ^ (i + 2) / (Nat.factorial (i + 2) : ℝ) with hρk
    have hρ0 : 0 ≤ ρk := by positivity
    have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) hi
    have hc := Real.MatExp.corrCoeff_le_sub hi hlam0
    have hc0 : lam ^ (i + 2) - lam ≤ 0 := sub_nonpos.mpr (pow_le_of_le_one hlam0 hlam1 (by omega))
    -- the weight times `r^k/k!` lies in `[cLo, 0]`
    have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) (i + 2))
        (MatExp.taylorCoeffBounds r (i + 2)).sup) ≤ (lam ^ (i + 2) - lam) * ρk :=
      le_trans (mulDown_le_mul _ _) (le_trans
        (mul_le_mul_of_nonpos_left hhi (le_trans hκ (hc.trans hc0)))
        (mul_le_mul_of_nonneg_right (hκ.trans hc) hρ0))
    have hhi' : (lam ^ (i + 2) - lam) * ρk ≤ toReal (zero : 𝕋) := by
      rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ0
    have hmem := Real.Interval.mem_mat_iff.mp (Interval.smul_outer hlo hhi' _ (hNmem (i + 2))) j k
    have hval : ((lam ^ (i + 2) - lam) * ρk) • ((rr ^ (i + 2))⁻¹
        • ((Nat.factorial (i + 2) : ℝ) • Q (i + 2))) = Cf i := by
      simp only [hCf, smul_smul, hρk]
      congr 1
      field_simp
    rw [hval] at hmem
    simp only [Interval.nominal, RealImage.realImage, toRealMat] at hmem
    rw [MatExp.intervalCorrTerm, Interval.materialiseMat_eq]
    exact ⟨(min_le_left _ _).trans hmem.1, hmem.2.trans (le_max_left _ _)⟩
  refine ⟨_, hΦ, _, hF, ?_⟩
  -- and the two together are the expansion, order by order
  have hexp : ∑ k ∈ Finset.range (η + 1), Real.MatExp.peanoBakerTerm Â k t *ᵥ x₀ + ρ
      = ∑ k ∈ Finset.range (η + 1), lam ^ k • (Q k *ᵥ x₀) + E *ᵥ x₀ := by
    rw [hEv]
    simp only [← Matrix.smul_mulVec, ← hPQ]
  have hQ0 : Q 0 = 1 := by simp [hQ, Real.MatExp.peanoBakerTerm]
  have hsplit : ∀ f : ℕ → Vec ℝ n, ∑ k ∈ Finset.range (η + 1), f k
      = f 0 + f 1 + ∑ i ∈ Finset.range (η - 1), f (i + 2) := fun f => by
    rw [hη, show m + 2 + 1 = m + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ', show m + 2 - 1 = m + 1 by omega]
    abel
  rw [hexp, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.sum_mulVec, hsplit, hsplit]
  simp only [hCf, hQ0, Matrix.one_mulVec, pow_zero, pow_one, one_smul, sub_smul,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Finset.sum_sub_distrib, smul_add, Finset.smul_sum]
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

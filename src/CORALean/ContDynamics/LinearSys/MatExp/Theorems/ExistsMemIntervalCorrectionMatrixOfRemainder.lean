module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulVecEqOfNormLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RescaledPeanoBakerTermMemMatPow
public import CORALean.ContSet.Interval.Real.Theorems.AbsMaxSmul
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# The truncated Peano–Baker series plus a short remainder is CORA's interpolation

The core of `exists_mem_intervalCorrectionMatrix_of_integral`, stated of the expansion rather
than of a run, so a run with an input can use it for its homogeneous half. With every `A(σ)` in
`B`, the first `η + 1` Peano–Baker terms at `t ∈ [0, r]` applied to `x₀`, plus any `ρ` no longer
than `‖x₀‖` times the remainder bound at `t • B`, are the straight line `(1 - λ) x₀ + λ Φ x₀` to
a member `Φ` of the step's exponential enclosure plus `F x₀` for a member `F` of the correction
matrix, `λ = t / r`. The `k`-th term is `λ^k` times `Q_k = (r/t)^k P_k(t)`, and `k! Q_k` lies in
the `k`-th power of `r • B`; the correction keeps `(λ^k - λ) Q_k` from order `2` on, with
`λ^k - λ ∈ [corrCoeff k, 0]` the interval of CORA's `priv_tie`. `ρ` is `F`'s widening.

## Inputs
* `B` – interval matrix
* `A` – time-varying matrix
* `r` – step length
* `m` – Taylor order offset
* `t` – time
* `x₀` – start vector
* `ρ` – remainder vector

## Hypotheses
* `hA` – matrix entries integrable
* `hAB` – matrix stays in the box
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `ht0` – time nonnegative
* `htr` – time within the step
* `hρ` – remainder short enough

## Conclusion
* the truncated series plus remainder is an interpolation plus a correction member
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `1/k!` times a member of the `k`-th power of `r • B`, weighted by
`κ ∈ [corrCoeff k, 0]`, lies between the order's correction term and zero. -/
theorem aux_corr_entry {B : Interval (Mat ℝ n n)} {r κ : ℝ} {k : ℕ} {N : Mat ℝ n n}
    (hr : 0 ≤ r) (hN : N ∈ (Interval.matPow (Interval.smul r B) k).construct)
    (hκ1 : MatExp.corrCoeff k ≤ κ) (hκ2 : κ ≤ 0) (i j : Fin n) : -- --- CONCL ---
    min ((MatExp.intervalCorrTerm B r k).inf i j) 0
        ≤ κ * ((Nat.factorial k : ℝ)⁻¹ * N i j) ∧
      κ * ((Nat.factorial k : ℝ)⁻¹ * N i j)
        ≤ max ((MatExp.intervalCorrTerm B r k).sup i j) 0 := by -- --- PROOF ---
  have hsr := Interval.matPow_smul B hr k
  have hm := Interval.mem_mat_iff.mp hN i j
  rw [hsr.1, hsr.2] at hm
  simp only [Matrix.smul_apply, smul_eq_mul] at hm
  have hf : (0:ℝ) ≤ (Nat.factorial k : ℝ)⁻¹ := by positivity
  -- the weight and the entry each range over an interval; the corners bound the product
  have hc := Interval.mul_between_corners hκ1 hκ2
    (mul_le_mul_of_nonneg_left hm.1 hf) (mul_le_mul_of_nonneg_left hm.2 hf)
  simp only [Interval.mulLo, Interval.mulHi, zero_mul, min_self, max_self] at hc
  simp only [MatExp.intervalCorrTerm, Interval.smul, Entrywise.ofEntry, Entrywise.entry]
  have e : ∀ v : ℝ, MatExp.corrCoeff k * r ^ k * (Nat.factorial k : ℝ)⁻¹ * v
      = MatExp.corrCoeff k * ((Nat.factorial k : ℝ)⁻¹ * (r ^ k * v)) := fun v => by ring
  rw [e, e]
  exact hc


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first `η + 1` Peano–Baker terms of a matrix that stays in `B`, applied to
`x₀` and widened by a short `ρ`, are the interpolation from `x₀` to a member of the
step's exponential enclosure, plus a member of the correction matrix applied to `x₀`. -/
theorem MatExp.exists_mem_intervalCorrectionMatrix_of_remainder {B : Interval (Mat ℝ n n)}
    {A : ℝ → Mat ℝ n n} (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖(Interval.smul r B).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (x₀ ρ : Vec ℝ n)
    (hρ : ‖ρ‖ ≤ ‖x₀‖ * MatExp.expRemainderBound (Interval.smul t B).absMax (m + 2)) :
    ∃ Φ ∈ (MatExp.expIntervalEnclosure (Interval.smul r B) (m + 2)).construct,
      ∃ F ∈ (MatExp.intervalCorrectionMatrix B r (m + 2)).construct,
        ∑ k ∈ Finset.range (m + 2 + 1), MatExp.peanoBakerTerm A k t *ᵥ x₀ + ρ
          = ((1 - t / r) • x₀ + (t / r) • (Φ *ᵥ x₀)) + F *ᵥ x₀ := by -- --- PROOF ---
  set η := m + 2 with hη
  set R := MatExp.expRemainderBound (Interval.smul r B).absMax η with hRdef
  have hεr : ‖(Interval.smul r B).absMax‖ / ((η : ℝ) + 2) < 1 := hε
  have hR0 : 0 ≤ R := by
    have h1 : 0 < 1 - ‖(Interval.smul r B).absMax‖ / ((η : ℝ) + 2) := by linarith
    rw [hRdef, MatExp.expRemainderBound]; positivity
  -- the remainder, a vector, becomes the correction's widening
  have habs : ‖(Interval.smul t B).absMax‖ ≤ ‖(Interval.smul r B).absMax‖ := by
    rw [Interval.absMax_smul B ht0, Interval.absMax_smul B hr.le, norm_smul, norm_smul,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hRt := MatExp.expRemainderBound_mono η habs hεr
  obtain ⟨E, hE, hEv⟩ := exists_mulVec_eq_of_norm_le hR0
    (hρ.trans (mul_le_mul_of_nonneg_left hRt (norm_nonneg _)))
  -- the correction's kept orders, summed, and the widening `E` on top
  have hFE : ∀ C : Mat ℝ n n, (∀ i j,
      ∑ k ∈ Finset.range (η - 1), min ((MatExp.intervalCorrTerm B r (k + 2)).inf i j) 0
          ≤ C i j ∧
        C i j ≤ ∑ k ∈ Finset.range (η - 1),
          max ((MatExp.intervalCorrTerm B r (k + 2)).sup i j) 0) →
      C + E ∈ (MatExp.intervalCorrectionMatrix B r η).construct := by
    intro C hC
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have hEij := abs_le.mp (hE i j)
    simp only [MatExp.intervalCorrectionMatrix, Matrix.add_apply]
    constructor <;> linarith [(hC i j).1, (hC i j).2, hEij.1, hEij.2]
  rcases ht0.eq_or_lt with rfl | ht
  · -- at the start of the step the terms are the identity, and the widening is all of `F`
    refine ⟨exp (r • A 0), MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer r B (hAB 0)) hεr, 0 + E, hFE 0 fun i j => ⟨?_, ?_⟩, ?_⟩
    · exact Finset.sum_nonpos fun k _ => min_le_right _ 0
    · exact Finset.sum_nonneg fun k _ => le_max_right _ 0
    have hz : (Matrix.of fun _ _ => (0:ℝ) : Mat ℝ n n) = 0 := rfl
    rw [Finset.sum_range_succ', zero_add, hEv]
    simp [MatExp.peanoBakerTerm, hz]
  set lam := t / r with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht.le hr.le
  have hlam1 : lam ≤ 1 := (div_le_one hr).mpr htr
  set Q : ℕ → Mat ℝ n n := fun k => (r / t) ^ k • MatExp.peanoBakerTerm A k t with hQ
  have hQmem : ∀ k, (Nat.factorial k : ℝ) • Q k
      ∈ (Interval.matPow (Interval.smul r B) k).construct := fun k =>
    MatExp.rescaled_peanoBakerTerm_mem_matPow hA hAB k ht hr.le
  have hPQ : ∀ k, MatExp.peanoBakerTerm A k t = lam ^ k • Q k := fun k => by
    simp only [hQ, hlam, smul_smul, ← mul_pow,
      div_mul_div_comm, mul_comm t r, div_self (mul_ne_zero hr.ne' ht.ne'), one_pow, one_smul]
  -- the mapping matrix: the rescaled terms, each in its order of `r • B`'s Taylor box
  have hΦ : ∑ k ∈ Finset.range (η + 1), Q k
      ∈ (MatExp.expIntervalEnclosure (Interval.smul r B) η).construct := by
    have hterm : ∀ k, Q k ∈ (Interval.smul ((Nat.factorial k : ℝ)⁻¹)
        (Interval.matPow (Interval.smul r B) k)).construct := fun k => by
      have h := Interval.smul_outer ((Nat.factorial k : ℝ)⁻¹) _ (hQmem k)
      rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h
    have htay : ∀ η', ∑ k ∈ Finset.range (η' + 1), Q k
        ∈ (MatExp.expIntervalTaylor (Interval.smul r B) η').construct := by
      intro η'
      induction η' with
      | zero => rw [Finset.sum_range_one]; exact hterm 0
      | succ k ih =>
        have h := Interval.plus_outer _ _ (Set.add_mem_add (hterm (k + 1)) ih)
        rw [add_comm (Q (k + 1)), ← Finset.sum_range_succ] at h
        exact h
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have h := Interval.mem_mat_iff.mp (htay η) i j
    show (MatExp.expIntervalTaylor _ η).inf i j - R ≤ _ ∧
      _ ≤ (MatExp.expIntervalTaylor _ η).sup i j + R
    constructor <;> linarith [h.1, h.2]
  -- the correction: orders `2 … η`, each weighted by `λ^k - λ`, plus the widening
  set C := ∑ i ∈ Finset.range (η - 1), (lam ^ (i + 2) - lam) • Q (i + 2) with hC
  have hF : C + E ∈ (MatExp.intervalCorrectionMatrix B r η).construct := by
    refine hFE C fun i j => ?_
    have hterm : ∀ k ∈ Finset.range (η - 1),
        min ((MatExp.intervalCorrTerm B r (k + 2)).inf i j) 0
            ≤ ((lam ^ (k + 2) - lam) • Q (k + 2)) i j ∧
          ((lam ^ (k + 2) - lam) • Q (k + 2)) i j
            ≤ max ((MatExp.intervalCorrTerm B r (k + 2)).sup i j) 0 := by
      intro k _
      -- the weight `λ^k - λ` lies in `[corrCoeff k, 0]`, the interval of `priv_tie`
      have hκ1 := MatExp.corrCoeff_le_sub (i := k + 2) (by omega) hlam0
      have hκ2 : lam ^ (k + 2) - lam ≤ 0 :=
        sub_nonpos.mpr (pow_le_of_le_one hlam0 hlam1 (by omega))
      have h := aux_corr_entry hr.le (hQmem (k + 2)) hκ1 hκ2 i j
      have hv : ((lam ^ (k + 2) - lam) • Q (k + 2)) i j = (lam ^ (k + 2) - lam)
          * ((Nat.factorial (k + 2) : ℝ)⁻¹ * ((Nat.factorial (k + 2) : ℝ) • Q (k + 2)) i j) := by
        simp only [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [hv]; exact h
    -- summed over the kept orders
    have hCij : C i j = ∑ k ∈ Finset.range (η - 1),
        ((lam ^ (k + 2) - lam) • Q (k + 2)) i j := by rw [hC, Matrix.sum_apply]
    rw [hCij]
    exact ⟨Finset.sum_le_sum fun k hk => (hterm k hk).1,
      Finset.sum_le_sum fun k hk => (hterm k hk).2⟩
  refine ⟨_, hΦ, C + E, hF, ?_⟩
  -- and the two together are the expansion, order by order
  have hexp : ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t *ᵥ x₀ + ρ
      = ∑ k ∈ Finset.range (η + 1), lam ^ k • (Q k *ᵥ x₀) + E *ᵥ x₀ := by
    rw [hEv]
    simp only [← Matrix.smul_mulVec, ← hPQ]
  have hQ0 : Q 0 = 1 := by simp [hQ, MatExp.peanoBakerTerm]
  -- orders `0` and `1` split off, the rest indexed from `2` as the correction is
  have hsplit : ∀ f : ℕ → Vec ℝ n, ∑ k ∈ Finset.range (η + 1), f k
      = f 0 + f 1 + ∑ i ∈ Finset.range (η - 1), f (i + 2) := fun f => by
    rw [hη, show m + 2 + 1 = m + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ', show m + 2 - 1 = m + 1 by omega]
    abel
  rw [hexp, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.sum_mulVec, hsplit, hsplit]
  simp only [hQ0, Matrix.one_mulVec, pow_zero, pow_one, one_smul, sub_smul,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Finset.sum_sub_distrib, smul_add, Finset.smul_sum]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

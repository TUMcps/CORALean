import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMulVecEqOfNormLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSubPeanoBakerSumLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerTermMemMatPow
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

/-!
# A run inside a box, between the two ends of a step, is CORA's interpolation

`expDiff_mem_intervalCorrectionMatrix` for a matrix that varies in time. A
solution of `x(s) = x(0) + ∫₀ˢ A(σ) x(σ) dσ` on `[0, r]`, every `A(σ)` in `B`, is
at every `t ∈ [0, r]` the straight line `(1 - λ) x(0) + λ Φ x(0)` from its start
to a member `Φ` of the step's exponential enclosure, plus `F x(0)` for a member `F`
of the correction matrix, `λ = t / r` — the very two interval matrices
`'constParam'` uses, which is what CORA's `initReach` computes for `'varParam'`.

The `k`-th Peano–Baker term at `t` is `λ^k` times `Q_k = (r/t)^k P_k(t)`, and
`k! Q_k` lies in the `k`-th power of `r • B`, because the box admits a different
member at every factor. So `Φ` is the sum of the `Q_k`, and the correction keeps
`(λ^k - λ) Q_k` from order `2` on, `λ^k - λ ∈ [corrCoeff k, 0]` being exactly the
interval CORA's `priv_tie` multiplies the powers by; order `1` needs no
correction, `λ^1 = λ`. The Picard remainder past order `η` goes into `F`'s
widening, the remainder bound at `t • B` being no larger than at `r • B`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A term rescaled from `t` to `r`, times `k!`, lies in the `k`-th power of
`r • B`. -/
theorem aux_rescaled_mem {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) (k : ℕ) {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (Nat.factorial k : ℝ) • ((r / t) ^ k • MatExp.peanoBakerTerm A k t)
      ∈ (Interval.matPow (Interval.smul r B) k).construct := by -- --- PROOF ---
  have hm := Interval.mem_mat_iff.mp (MatExp.peanoBakerTerm_mem_matPow hA hAB k ht.le)
  have hst := Interval.matPow_smul B ht.le k
  have hsr := Interval.matPow_smul B hr k
  have hq : 0 ≤ (r / t) ^ k := by positivity
  have hscale : (r / t) ^ k * t ^ k = r ^ k := by rw [← mul_pow, div_mul_cancel₀ _ ht.ne']
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  obtain ⟨h1, h2⟩ := hm i j
  rw [hst.1] at h1
  rw [hst.2] at h2
  rw [hsr.1, hsr.2]
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
  -- the bounds at `t` scaled by `(r/t)^k` are the bounds at `r`
  constructor
  · calc r ^ k * (Interval.matPow B k).inf i j
        = (r / t) ^ k * (t ^ k * (Interval.matPow B k).inf i j) := by rw [← hscale]; ring
      _ ≤ (r / t) ^ k * ((Nat.factorial k : ℝ) * MatExp.peanoBakerTerm A k t i j) :=
          mul_le_mul_of_nonneg_left h1 hq
      _ = _ := by ring
  · calc _ = (r / t) ^ k * ((Nat.factorial k : ℝ) * MatExp.peanoBakerTerm A k t i j) := by ring
      _ ≤ (r / t) ^ k * (t ^ k * (Interval.matPow B k).sup i j) :=
          mul_le_mul_of_nonneg_left h2 hq
      _ = r ^ k * (Interval.matPow B k).sup i j := by rw [← hscale]; ring

/-- `1/k!` times a member of the `k`-th power of `r • B`, weighted by
`κ ∈ [corrCoeff k, 0]`, lies between the order's correction term and zero. -/
theorem aux_corr_entry {B : Interval (Mat ℝ n n)} {r κ : ℝ} {k : ℕ} {N : Mat ℝ n n}
    (hr : 0 ≤ r) (hN : N ∈ (Interval.matPow (Interval.smul r B) k).construct)
    (hκ1 : MatExp.corrCoeff k ≤ κ) (hκ2 : κ ≤ 0) (i j : Fin n) :
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

/-- A solution of the integral equation at a matrix that stays in `B` is, at every
time of the step, the interpolation from its start to a member of the step's
exponential enclosure, plus a member of the correction matrix applied to its start. -/
theorem MatExp.exists_mem_intervalCorrectionMatrix_of_integral {B : Interval (Mat ℝ n n)}
    {A : ℝ → Mat ℝ n n} (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {x : ℝ → Vec ℝ n} {r : ℝ} (hr : 0 < r)
    (hxc : ContinuousOn x (Set.Icc 0 r))
    (hx : ∀ s ∈ Set.Icc 0 r, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) {m : ℕ}
    (hε : ‖(Interval.smul r B).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    ∃ Φ ∈ (MatExp.expIntervalEnclosure (Interval.smul r B) (m + 2)).construct,
      ∃ F ∈ (MatExp.intervalCorrectionMatrix B r (m + 2)).construct,
        x t = ((1 - t / r) • x 0 + (t / r) • (Φ *ᵥ x 0)) + F *ᵥ x 0 := by -- --- PROOF ---
  set η := m + 2 with hη
  set R := MatExp.expRemainderBound (Interval.smul r B).absMax η with hRdef
  have hεr : ‖(Interval.smul r B).absMax‖ / ((η : ℝ) + 2) < 1 := hε
  have hR0 : 0 ≤ R := by
    have h1 : 0 < 1 - ‖(Interval.smul r B).absMax‖ / ((η : ℝ) + 2) := by linarith
    rw [hRdef, MatExp.expRemainderBound]; positivity
  -- zero lies in the correction matrix: every kept order straddles zero
  have hF0 : (0 : Mat ℝ n n) ∈ (MatExp.intervalCorrectionMatrix B r η).construct := by
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    simp only [MatExp.intervalCorrectionMatrix, Matrix.zero_apply]
    constructor
    · linarith [Finset.sum_nonpos fun k (_ : k ∈ Finset.range (η - 1)) =>
        min_le_right ((MatExp.intervalCorrTerm B r (k + 2)).inf i j) 0]
    · linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.range (η - 1)) =>
        le_max_right ((MatExp.intervalCorrTerm B r (k + 2)).sup i j) 0]
  rcases ht0.eq_or_lt with rfl | ht
  · -- at the start of the step the interpolation is the start itself
    refine ⟨exp (r • A 0), MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer r B (hAB 0)) hεr, 0, hF0, ?_⟩
    simp
  set lam := t / r with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht.le hr.le
  have hlam1 : lam ≤ 1 := (div_le_one hr).mpr htr
  set Q : ℕ → Mat ℝ n n := fun k => (r / t) ^ k • MatExp.peanoBakerTerm A k t with hQ
  have hQmem : ∀ k, (Nat.factorial k : ℝ) • Q k
      ∈ (Interval.matPow (Interval.smul r B) k).construct := fun k =>
    aux_rescaled_mem hA hAB k ht hr.le
  have hPQ : ∀ k, MatExp.peanoBakerTerm A k t = lam ^ k • Q k := fun k => by
    simp only [hQ, hlam, smul_smul, ← mul_pow,
      div_mul_div_comm, mul_comm t r, div_self (mul_ne_zero hr.ne' ht.ne'), one_pow, one_smul]
  -- the Picard remainder at `t`, a vector, becomes the correction's widening
  have habs : ‖(Interval.smul t B).absMax‖ ≤ ‖(Interval.smul r B).absMax‖ := by
    rw [Interval.absMax_smul B ht.le, Interval.absMax_smul B hr.le, norm_smul, norm_smul,
      Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hεt : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hεr
  have hρ := MatExp.norm_sub_peanoBakerSum_le hA hAB ht.le
    (hxc.mono (Set.Icc_subset_Icc le_rfl htr)) (fun s hs => hx s ⟨hs.1, hs.2.trans htr⟩) η hεt
  have hRt := MatExp.expRemainderBound_mono η habs hεr
  obtain ⟨E, hE, hEv⟩ := exists_mulVec_eq_of_norm_le hR0
    (hρ.trans (mul_le_mul_of_nonneg_left hRt (norm_nonneg _)))
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
    refine Interval.mem_mat_iff.mpr fun i j => ?_
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
    -- summed over the kept orders, then widened by the remainder's entries
    have hlo := Finset.sum_le_sum fun k hk => (hterm k hk).1
    have hhi := Finset.sum_le_sum fun k hk => (hterm k hk).2
    have hEij := abs_le.mp (hE i j)
    have hCij : C i j = ∑ k ∈ Finset.range (η - 1), ((lam ^ (k + 2) - lam) • Q (k + 2)) i j := by
      rw [hC, Matrix.sum_apply]
    simp only [MatExp.intervalCorrectionMatrix, Matrix.add_apply]
    rw [hCij]
    constructor <;> linarith [hEij.1, hEij.2]
  refine ⟨_, hΦ, C + E, hF, ?_⟩
  -- and the two together are the expansion, order by order
  have hexp : x t = ∑ k ∈ Finset.range (η + 1), lam ^ k • (Q k *ᵥ x 0) + E *ᵥ x 0 := by
    rw [hEv]
    simp only [← Matrix.smul_mulVec, ← hPQ, ← Matrix.sum_mulVec]
    abel
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

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousPeanoBakerInputTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntegralPowDivFactorialMul
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulPeanoBakerTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumLeExpTail
public import CORALean.ContSet.Interval.Real.Theorems.AbsMaxSmul
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import Mathlib.Topology.Algebra.Order.Floor

@[expose] public section

/-!
# The Peano–Baker expansion of a run with an input, and what it leaves

A solution of `x(s) = x(0) + ∫₀ˢ A(σ) x(σ) + u(σ) dσ` on `[0, t]`, every `A(σ)` in
the box `B` and `‖u‖ ≤ ν`, is its first `η + 1` Peano–Baker terms applied to
`x(0)` plus the first `η + 1` terms of its input, each within its own remainder:
`‖x(0)‖` respectively `t ν` times `expRemainderBound` at `t • B` — the exponential's
own tail, not `e^{ct}` times it as a Grönwall step would give.

Picard's iteration on the state: what `L` orders leave is `∫₀ˢ A(σ)` of what `L - 1`
left, so at most `X (c s)^L / L!` with `c = ‖B.absMax‖` and `X` a bound on the run,
and it vanishes. The orders past `η` of both series are summable, each under its
term of the exponential series of `c t`, and their sums are the two remainders.

`Vec` carries the sup norm, and `‖A(σ)‖` is the `l∞` operator norm it induces.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory Filter

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coordinate of an integral is the integral of the coordinate. -/
theorem aux_pb_integral_apply {f : ℝ → Vec ℝ n} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (i : Fin n) :
    (∫ s in a..b, f s) i = ∫ s in a..b, f s i :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).intervalIntegral_comp_comm
    hf).symm

/-- A term applied to a fixed vector is continuous in time. -/
theorem aux_pb_continuous_mulVec {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) (k : ℕ) (v : Vec ℝ n) :
    Continuous fun σ => MatExp.peanoBakerTerm A k σ *ᵥ v := by
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ =>
    (MatExp.continuous_peanoBakerTerm hA k i j).mul continuous_const

/-- The recursion read on a vector: `P_{k+1}(s) v = ∫₀ˢ A(σ) (P_k(σ) v) dσ`. -/
theorem aux_pb_succ_mulVec {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) (k : ℕ) (s : ℝ)
    (v : Vec ℝ n) : -- --- STMT ---
    MatExp.peanoBakerTerm A (k + 1) s *ᵥ v
      = ∫ σ in (0:ℝ)..s, A σ *ᵥ (MatExp.peanoBakerTerm A k σ *ᵥ v) := by -- --- PROOF ---
  funext i
  rw [aux_pb_integral_apply
    (MatExp.intervalIntegrable_mulVec hA (aux_pb_continuous_mulVec hA k v).continuousOn) i]
  simp only [Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, MatExp.peanoBakerTerm, Matrix.of_apply]
  -- the coordinate sum and the integral commute, each summand integrable
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (MatExp.intervalIntegrable_mul_peanoBakerTerm hA k i j 0 s).mul_const _]
  exact Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_mul_const _ _).symm

/-- A member of the box stretches a vector by at most `‖B.absMax‖`. -/
theorem aux_pb_norm_mulVec_le {B : Interval (Mat ℝ n n)} {M : Mat ℝ n n}
    (hM : M ∈ B.construct) (w : Vec ℝ n) : ‖M *ᵥ w‖ ≤ ‖B.absMax‖ * ‖w‖ :=
  le_trans (Matrix.linfty_opNorm_mulVec _ _)
    (mul_le_mul_of_nonneg_right (Interval.norm_le_absMax hM) (norm_nonneg _))

/-- `‖P_k(s) v‖ ≤ s^k/k! · c^k ‖v‖`, the `k`-th term of the exponential of `c s`. -/
theorem aux_pb_norm_term_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) (v : Vec ℝ n) (k : ℕ) : -- --- STMT ---
    ∀ s, 0 ≤ s → ‖MatExp.peanoBakerTerm A k s *ᵥ v‖
      ≤ s ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ k * ‖v‖) := by -- --- PROOF ---
  induction k with
  | zero => intro s _; simp [MatExp.peanoBakerTerm]
  | succ k ih =>
    intro s hs
    rw [aux_pb_succ_mulVec hA, ← MatExp.integral_pow_div_factorial_mul]
    -- the integrand is under `c` times the bound one order down
    refine intervalIntegral.norm_integral_le_of_norm_le hs
      (Filter.Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ (k + 1) * ‖v‖)).intervalIntegrable _ _)
    refine le_trans (aux_pb_norm_mulVec_le (hAB σ) _) ?_
    calc ‖B.absMax‖ * ‖MatExp.peanoBakerTerm A k σ *ᵥ v‖
        ≤ ‖B.absMax‖ * (σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ k * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (ih σ hσ.1.le) (norm_nonneg _)
      _ = σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ (k + 1) * ‖v‖) := by ring


/-- `‖V_k(s)‖ ≤ s^{k+1}/(k+1)! · c^k ν`, the input's terms. -/
theorem aux_pb_norm_input_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hAB : ∀ s, A s ∈ B.construct) {u : ℝ → Vec ℝ n} {t ν : ℝ}
    (hν : ∀ s ∈ Set.Icc 0 t, ‖u s‖ ≤ ν) (k : ℕ) : -- --- STMT ---
    ∀ s ∈ Set.Icc 0 t, ‖MatExp.peanoBakerInputTerm A u k s‖
      ≤ s ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * (‖B.absMax‖ ^ k * ν) := by -- --- PROOF ---
  induction k with
  | zero =>
    intro s hs
    show ‖∫ σ in (0:ℝ)..s, u σ‖ ≤ _
    rw [← MatExp.integral_pow_div_factorial_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hs.1
      (Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ 0 / (Nat.factorial 0 : ℝ) * (‖B.absMax‖ ^ 0 * ν)).intervalIntegrable _ _)
    simpa using hν σ ⟨hσ.1.le, hσ.2.trans hs.2⟩
  | succ k ih =>
    -- one more factor in `B` costs `c`, and the integral one more order
    intro s hs
    show ‖∫ σ in (0:ℝ)..s, A σ *ᵥ MatExp.peanoBakerInputTerm A u k σ‖ ≤ _
    rw [← MatExp.integral_pow_div_factorial_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hs.1
      (Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)
          * (‖B.absMax‖ ^ (k + 1) * ν)).intervalIntegrable _ _)
    refine le_trans (aux_pb_norm_mulVec_le (hAB σ) _) ?_
    calc ‖B.absMax‖ * ‖MatExp.peanoBakerInputTerm A u k σ‖
        ≤ ‖B.absMax‖ * (σ ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * (‖B.absMax‖ ^ k * ν)) :=
          mul_le_mul_of_nonneg_left (ih σ ⟨hσ.1.le, hσ.2.trans hs.2⟩) (norm_nonneg _)
      _ = _ := by ring

/-- What `L + 1` orders of both series leave is `∫₀ˢ A(σ)` of what `L` orders leave. -/
theorem aux_pb_remainder_succ {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b) {u : ℝ → Vec ℝ n}
    (hu : ∀ a b, IntervalIntegrable u volume a b)
    {x : ℝ → Vec ℝ n} {t : ℝ} (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (A σ *ᵥ x σ + u σ)) (L : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 t) : -- --- STMT ---
    x s - ∑ j ∈ Finset.range (L + 1), (MatExp.peanoBakerTerm A j s *ᵥ x 0
        + MatExp.peanoBakerInputTerm A u j s)
      = ∫ σ in (0:ℝ)..s, A σ *ᵥ (x σ - ∑ j ∈ Finset.range L,
          (MatExp.peanoBakerTerm A j σ *ᵥ x 0
            + MatExp.peanoBakerInputTerm A u j σ)) := by -- --- PROOF ---
  have hxs : ContinuousOn x (Set.uIcc 0 s) := hxc.mono (by
    rw [Set.uIcc_of_le hs.1]; exact Set.Icc_subset_Icc le_rfl hs.2)
  have hPc := fun j => aux_pb_continuous_mulVec hA j (x 0)
  have hVc := fun j => MatExp.continuous_peanoBakerInputTerm hA hu j
  simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_add]
  have hsum := IntervalIntegrable.sum (Finset.range L) fun j _ =>
    (MatExp.intervalIntegrable_mulVec hA (a := 0) (b := s) (hPc j).continuousOn).add
      (MatExp.intervalIntegrable_mulVec hA (a := 0) (b := s) (hVc j).continuousOn)
  rw [Finset.sum_fn] at hsum
  -- split the integral, then read each order's integral as the next order
  rw [intervalIntegral.integral_sub (MatExp.intervalIntegrable_mulVec hA hxs) hsum,
    intervalIntegral.integral_finsetSum fun j _ =>
      (MatExp.intervalIntegrable_mulVec hA (hPc j).continuousOn).add
        (MatExp.intervalIntegrable_mulVec hA (hVc j).continuousOn),
    Finset.sum_range_succ']
  simp only [fun j => intervalIntegral.integral_add
    (MatExp.intervalIntegrable_mulVec hA (a := 0) (b := s) (hPc j).continuousOn)
    (MatExp.intervalIntegrable_mulVec hA (a := 0) (b := s) (hVc j).continuousOn),
    ← aux_pb_succ_mulVec hA]
  conv_lhs => rw [hx s hs, intervalIntegral.integral_add
    (MatExp.intervalIntegrable_mulVec hA hxs) (hu 0 s)]
  simp only [MatExp.peanoBakerTerm, MatExp.peanoBakerInputTerm, Matrix.one_mulVec]
  abel

/-- What `L` orders leave is at most `X (c s)^L / L!`, `X` bounding the run. -/
theorem aux_pb_remainder_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {u : ℝ → Vec ℝ n}
    (hu : ∀ a b, IntervalIntegrable u volume a b)
    {x : ℝ → Vec ℝ n} {t : ℝ} (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (A σ *ᵥ x σ + u σ)) {X : ℝ}
    (hX : ∀ s ∈ Set.Icc 0 t, ‖x s‖ ≤ X) (L : ℕ) : -- --- STMT ---
    ∀ s ∈ Set.Icc 0 t, ‖x s - ∑ j ∈ Finset.range L,
        (MatExp.peanoBakerTerm A j s *ᵥ x 0 + MatExp.peanoBakerInputTerm A u j s)‖
      ≤ s ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ L * X) := by -- --- PROOF ---
  induction L with
  | zero => intro s hs; simpa using hX s hs
  | succ L ih =>
    intro s hs
    rw [aux_pb_remainder_succ hA hu hxc hx L hs, ← MatExp.integral_pow_div_factorial_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hs.1
      (Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ (L + 1) * X)).intervalIntegrable _ _)
    have hσ' : σ ∈ Set.Icc 0 t := ⟨hσ.1.le, hσ.2.trans hs.2⟩
    refine le_trans (aux_pb_norm_mulVec_le (hAB σ) _) ?_
    calc ‖B.absMax‖ * ‖x σ - ∑ j ∈ Finset.range L,
          (MatExp.peanoBakerTerm A j σ *ᵥ x 0 + MatExp.peanoBakerInputTerm A u j σ)‖
        ≤ ‖B.absMax‖ * (σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ L * X)) :=
          mul_le_mul_of_nonneg_left (ih σ hσ') (norm_nonneg _)
      _ = σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ (L + 1) * X) := by ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run inside `B` with an input bounded by `ν` is its first `η + 1` Peano–Baker
terms applied to `x(0)` and its input's first `η + 1` terms, each up to a remainder
of `‖x(0)‖` respectively `t ν` times the remainder bound at the box of the step. -/
theorem MatExp.exists_peanoBaker_expansion {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct) {u : ℝ → Vec ℝ n}
    (hu : ∀ a b, IntervalIntegrable u volume a b)
    {x : ℝ → Vec ℝ n} {t : ℝ} (ht : 0 ≤ t) (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (A σ *ᵥ x σ + u σ)) {ν : ℝ}
    (hν : ∀ s ∈ Set.Icc 0 t, ‖u s‖ ≤ ν) (η : ℕ)
    (hε : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1) : -- --- STMT ---
    ∃ ρh ρu : Vec ℝ n,
      ‖ρh‖ ≤ ‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η ∧
      ‖ρu‖ ≤ t * ν * MatExp.expRemainderBound (Interval.smul t B).absMax η ∧
      x t = (∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t *ᵥ x 0 + ρh)
        + (∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerInputTerm A u k t
          + ρu) := by -- --- PROOF ---
  obtain ⟨X, hX⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  have htt : t ∈ Set.Icc 0 t := ⟨ht, le_rfl⟩
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans (hν 0 ⟨le_rfl, ht⟩)
  set c := ‖B.absMax‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have habs : ‖(Interval.smul t B).absMax‖ = c * t := by
    rw [Interval.absMax_smul B ht, norm_smul, Real.norm_of_nonneg ht, mul_comm]
  rw [habs] at hε
  set R := MatExp.expRemainderBound (Interval.smul t B).absMax η with hR
  have hRe : R = (c * t) ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      * (1 - c * t / ((η : ℝ) + 2))⁻¹ := by rw [hR, MatExp.expRemainderBound, habs]
  -- the orders past `η` of both series, and the exponential series they stay under
  set p : ℕ → Vec ℝ n := fun i => MatExp.peanoBakerTerm A (i + (η + 1)) t *ᵥ x 0 with hp
  set v : ℕ → Vec ℝ n := fun i => MatExp.peanoBakerInputTerm A u (i + (η + 1)) t with hv
  set g : ℕ → ℝ := fun i => (c * t) ^ (i + (η + 1)) / (Nat.factorial (i + (η + 1)) : ℝ)
    with hg
  have hgs : Summable g :=
    (summable_nat_add_iff (f := fun i : ℕ => (c * t) ^ i / (Nat.factorial i : ℝ)) (η + 1)).mpr
      (Real.summable_pow_div_factorial (c * t))
  -- every later order of each series is under its term of the exponential series
  have hpb : ∀ i, ‖p i‖ ≤ ‖x 0‖ * g i := fun i => by
    refine le_trans (aux_pb_norm_term_le hA hAB (x 0) _ t ht) (le_of_eq ?_)
    simp only [hg, mul_pow]; ring
  have hvb : ∀ i, ‖v i‖ ≤ t * ν * g i := fun i => by
    refine le_trans (aux_pb_norm_input_le hAB hν _ t htt) ?_
    have hK : (Nat.factorial (i + (η + 1)) : ℝ) ≤ Nat.factorial (i + (η + 1) + 1) :=
      Nat.cast_le.mpr (Nat.factorial_le (by omega))
    have hKp : (0:ℝ) < Nat.factorial (i + (η + 1)) := by positivity
    calc t ^ (i + (η + 1) + 1) / (Nat.factorial (i + (η + 1) + 1) : ℝ)
          * (c ^ (i + (η + 1)) * ν)
        = t * ν * (c * t) ^ (i + (η + 1)) / (Nat.factorial (i + (η + 1) + 1) : ℝ) := by
          rw [mul_pow]; ring
      _ ≤ t * ν * (c * t) ^ (i + (η + 1)) / (Nat.factorial (i + (η + 1)) : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hKp hK
      _ = t * ν * g i := by simp only [hg]; ring
  -- so both are summable, and their sums under the closed form of the tail
  have hps : Summable p := Summable.of_norm_bounded (hgs.mul_left _) hpb
  have hvs : Summable v := Summable.of_norm_bounded (hgs.mul_left _) hvb
  have htail : ∀ s : ℝ, 0 ≤ s → ∑' i, s * g i ≤ s * R := fun s hs => by
    rw [hRe]
    exact tsum_le_expTail (mul_nonneg hc0 ht) hs η hε (fun i => by positivity)
      fun i => le_of_eq (by simp only [hg, div_eq_inv_mul])
  refine ⟨∑' i, p i, ∑' i, v i, ?_, ?_, ?_⟩
  · exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpb
      (hgs.mul_left _))).trans ((Summable.tsum_le_tsum hpb (Summable.of_nonneg_of_le
        (fun _ => norm_nonneg _) hpb (hgs.mul_left _)) (hgs.mul_left _)).trans
          (htail _ (norm_nonneg _)))
  · exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hvb
      (hgs.mul_left _))).trans ((Summable.tsum_le_tsum hvb (Summable.of_nonneg_of_le
        (fun _ => norm_nonneg _) hvb (hgs.mul_left _)) (hgs.mul_left _)).trans
          (htail _ (mul_nonneg ht hν0)))
  -- the expansion telescopes: what order `η` leaves is every later order of both
  have htel : ∀ m : ℕ,
      x t - ∑ k ∈ Finset.range (η + 1),
          (MatExp.peanoBakerTerm A k t *ᵥ x 0 + MatExp.peanoBakerInputTerm A u k t)
        = ∑ i ∈ Finset.range m, (p i + v i)
          + (x t - ∑ k ∈ Finset.range (m + (η + 1)),
              (MatExp.peanoBakerTerm A k t *ᵥ x 0 + MatExp.peanoBakerInputTerm A u k t)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, Finset.sum_range_succ, show m + 1 + (η + 1) = (m + (η + 1)) + 1 by ring,
        Finset.sum_range_succ]
      abel
  -- and the Picard remainder past order `m + η` vanishes as `m` grows
  have hlim : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (p i + v i)
      + (x t - ∑ k ∈ Finset.range (m + (η + 1)),
          (MatExp.peanoBakerTerm A k t *ᵥ x 0 + MatExp.peanoBakerInputTerm A u k t)))
      atTop (nhds ((∑' i, p i + ∑' i, v i) + 0)) := by
    refine ((hps.hasSum.add hvs.hasSum).tendsto_sum_nat).add ?_
    refine squeeze_zero_norm (fun m => (aux_pb_remainder_le hA hAB hu hxc hx hX _ t htt).trans
      (le_of_eq (by rw [mul_pow]; ring :
        t ^ (m + (η + 1)) / (Nat.factorial (m + (η + 1)) : ℝ) * (c ^ (m + (η + 1)) * X)
          = (c * t) ^ (m + (η + 1)) / (Nat.factorial (m + (η + 1)) : ℝ) * X))) ?_
    rw [← zero_mul X]
    exact ((FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).comp
      (tendsto_add_atTop_nat (η + 1))).mul_const X
  simp only [← htel] at hlim
  have heq := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [add_zero] at heq
  rw [Finset.sum_add_distrib] at heq
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

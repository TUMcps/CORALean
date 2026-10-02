import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntegralPowDivFactorialMul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulPeanoBakerTerm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumLeExpTail
import CORALean.ContSet.Interval.Real.Theorems.AbsMaxSmul
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The Peano–Baker series truncated at order `η`, and what it leaves

A solution of `x(s) = x(0) + ∫₀ˢ A(σ) x(σ) dσ` on `[0, t]`, with every `A(σ)` in
the box `B`, differs from its first `η + 1` Peano–Baker terms applied to `x(0)`
by at most `‖x(0)‖` times `expRemainderBound` at the box of the step `t • B` —
the tail `MatExp.expIntervalEnclosure` already pays for a constant member.

Picard's iteration on the state, never on the fundamental matrix: what is left
after `L` terms is `∫₀ˢ A(σ)` of what was left after `L - 1`, so it is at most
`X (c s)^L / L!` with `c = ‖B.absMax‖` and `X` any bound on the run. Peeling the
terms past `η` off one at a time, each at most `(c t)^k / k! ‖x(0)‖`, leaves a
Picard remainder that vanishes as the order grows, and the terms sum to under
the closed form `tsum_le_expTail` gives. So the bound is the exponential's own,
not `e^{ct}` times it as a Grönwall step would give.

`Vec` carries the sup norm, and `‖A(σ)‖` is the `l∞` operator norm it induces.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

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
    (v : Vec ℝ n) :
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
    (hAB : ∀ s, A s ∈ B.construct) (v : Vec ℝ n) (k : ℕ) :
    ∀ s, 0 ≤ s → ‖MatExp.peanoBakerTerm A k s *ᵥ v‖
      ≤ s ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ k * ‖v‖) := by -- --- PROOF ---
  induction k with
  | zero => intro s _; simp [MatExp.peanoBakerTerm]
  | succ k ih =>
    intro s hs
    rw [aux_pb_succ_mulVec hA, ← MatExp.integral_pow_div_factorial_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hs
      (Filter.Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ (k + 1) * ‖v‖)).intervalIntegrable _ _)
    refine le_trans (aux_pb_norm_mulVec_le (hAB σ) _) ?_
    calc ‖B.absMax‖ * ‖MatExp.peanoBakerTerm A k σ *ᵥ v‖
        ≤ ‖B.absMax‖ * (σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ k * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (ih σ hσ.1.le) (norm_nonneg _)
      _ = σ ^ k / (Nat.factorial k : ℝ) * (‖B.absMax‖ ^ (k + 1) * ‖v‖) := by ring

/-- What `L + 1` terms leave is `∫₀ˢ A(σ)` of what `L` terms leave. -/
theorem aux_pb_remainder_succ {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    {x : ℝ → Vec ℝ n} {t : ℝ} (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) (L : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 t) :
    x s - ∑ j ∈ Finset.range (L + 1), MatExp.peanoBakerTerm A j s *ᵥ x 0
      = ∫ σ in (0:ℝ)..s, A σ *ᵥ (x σ - ∑ j ∈ Finset.range L,
          MatExp.peanoBakerTerm A j σ *ᵥ x 0) := by -- --- PROOF ---
  have hxs : ContinuousOn x (Set.uIcc 0 s) := hxc.mono (by
    rw [Set.uIcc_of_le hs.1]; exact Set.Icc_subset_Icc le_rfl hs.2)
  have hPc := fun j => aux_pb_continuous_mulVec hA j (x 0)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_sum]
  have hsum := IntervalIntegrable.sum (Finset.range L) fun j _ =>
    MatExp.intervalIntegrable_mulVec hA (a := 0) (b := s) (hPc j).continuousOn
  rw [Finset.sum_fn] at hsum
  -- split the integral, then read each term's integral as the next term
  rw [intervalIntegral.integral_sub (MatExp.intervalIntegrable_mulVec hA hxs) hsum,
    intervalIntegral.integral_finsetSum fun j _ =>
      MatExp.intervalIntegrable_mulVec hA (hPc j).continuousOn,
    Finset.sum_range_succ']
  simp only [← aux_pb_succ_mulVec hA]
  conv_lhs => rw [hx s hs]
  simp only [MatExp.peanoBakerTerm, Matrix.one_mulVec]
  abel

/-- What `L` terms leave is at most `X (c s)^L / L!`, `X` bounding the run. -/
theorem aux_pb_remainder_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct)
    {x : ℝ → Vec ℝ n} {t : ℝ} (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) {X : ℝ}
    (hX : ∀ s ∈ Set.Icc 0 t, ‖x s‖ ≤ X) (L : ℕ) :
    ∀ s ∈ Set.Icc 0 t, ‖x s - ∑ j ∈ Finset.range L, MatExp.peanoBakerTerm A j s *ᵥ x 0‖
      ≤ s ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ L * X) := by -- --- PROOF ---
  induction L with
  | zero => intro s hs; simpa using hX s hs
  | succ L ih =>
    intro s hs
    rw [aux_pb_remainder_succ hA hxc hx L hs, ← MatExp.integral_pow_div_factorial_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hs.1
      (Filter.Eventually.of_forall fun σ hσ => ?_)
      ((by fun_prop : Continuous fun σ : ℝ =>
        σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ (L + 1) * X)).intervalIntegrable _ _)
    have hσ' : σ ∈ Set.Icc 0 t := ⟨hσ.1.le, hσ.2.trans hs.2⟩
    refine le_trans (aux_pb_norm_mulVec_le (hAB σ) _) ?_
    calc ‖B.absMax‖ * ‖x σ - ∑ j ∈ Finset.range L, MatExp.peanoBakerTerm A j σ *ᵥ x 0‖
        ≤ ‖B.absMax‖ * (σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ L * X)) :=
          mul_le_mul_of_nonneg_left (ih σ hσ') (norm_nonneg _)
      _ = σ ^ L / (Nat.factorial L : ℝ) * (‖B.absMax‖ ^ (L + 1) * X) := by ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run inside `B` is its first `η + 1` Peano–Baker terms applied to `x(0)`,
to within `‖x(0)‖` times the remainder bound at the box of the step. -/
theorem MatExp.norm_sub_peanoBakerSum_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct)
    {x : ℝ → Vec ℝ n} {t : ℝ} (ht : 0 ≤ t) (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) (η : ℕ)
    (hε : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1) :
    ‖x t - ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t *ᵥ x 0‖
      ≤ ‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η := by -- --- PROOF ---
  obtain ⟨X, hX⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  have htt : t ∈ Set.Icc 0 t := ⟨ht, le_rfl⟩
  set c := ‖B.absMax‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have habs : ‖(Interval.smul t B).absMax‖ = c * t := by
    rw [Interval.absMax_smul B ht, norm_smul, Real.norm_of_nonneg ht, mul_comm]
  -- the expansion telescopes: what is left after order `η` is every later order
  have htel : ∀ m : ℕ,
      x t - ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t *ᵥ x 0
        = ∑ i ∈ Finset.range m, MatExp.peanoBakerTerm A (i + (η + 1)) t *ᵥ x 0
          + (x t - ∑ k ∈ Finset.range (m + (η + 1)),
              MatExp.peanoBakerTerm A k t *ᵥ x 0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, Finset.sum_range_succ, show m + 1 + (η + 1) = (m + (η + 1)) + 1 by ring,
        Finset.sum_range_succ]
      abel
  -- every later order is bounded by its term of the exponential series of `c t`
  set a : ℕ → ℝ := fun i =>
    ‖x 0‖ * ((c * t) ^ (i + (η + 1)) / (Nat.factorial (i + (η + 1)) : ℝ)) with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have hterm : ∀ i, ‖MatExp.peanoBakerTerm A (i + (η + 1)) t *ᵥ x 0‖ ≤ a i := fun i => by
    refine le_trans (aux_pb_norm_term_le hA hAB (x 0) _ t ht) (le_of_eq ?_)
    simp only [ha, mul_pow]; ring
  have hsa : Summable a :=
    ((summable_nat_add_iff (η + 1)).mpr (Real.summable_pow_div_factorial (c * t))).mul_left _
  have hR : ∑' i, a i ≤ ‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η := by
    rw [MatExp.expRemainderBound, habs]
    rw [habs] at hε
    exact tsum_le_expTail (mul_nonneg hc0 ht) (norm_nonneg _) η hε ha0
      fun i => le_of_eq (by simp only [ha, div_eq_inv_mul])
  -- the Picard remainder past order `m + η` vanishes as `m` grows
  have hlim : Filter.Tendsto (fun m : ℕ =>
      ‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η
        + (c * t) ^ (m + (η + 1)) / (Nat.factorial (m + (η + 1)) : ℝ) * X)
      Filter.atTop
      (nhds (‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η + 0)) := by
    refine tendsto_const_nhds.add ?_
    rw [← zero_mul X]
    exact ((FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).comp
      (Filter.tendsto_add_atTop_nat (η + 1))).mul_const X
  rw [add_zero] at hlim
  refine ge_of_tendsto' hlim fun m => ?_
  rw [htel m]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun i _ => hterm i)
      (le_trans (hsa.sum_le_tsum _ fun i _ => ha0 i) hR))
  · refine le_trans (aux_pb_remainder_le hA hAB hxc hx hX _ t htt) (le_of_eq ?_)
    rw [mul_pow]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

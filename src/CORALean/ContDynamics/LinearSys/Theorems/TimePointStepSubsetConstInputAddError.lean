module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralSubTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SumExpTailLe
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# What the step's end encloses beyond the states one held input reaches

`timePointStep_outer` run backwards, and sharper than
`timePointStep_subset_reach_add_error`: the exact point the enclosure is
measured against is reached by an input *held* at one member of `U`, so the set
on the right is `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U` and not the whole
`inputReach`. Every operand is a zonotope image, so that set is convex and
compact outright — which is what the inner approximation of a step needs and
what `inputReach` itself cannot supply.

At `Zonotope`, where `plus` and `mtimes` are exact — the class obligations are
one-directional, so nothing in this direction can be read off them.

Two terms, and only one is the remainder. What the enclosure adds past the
held-input point is: each Taylor order free to pick its own input, which no
trajectory is — second order in the step, untouched by the truncation order —
and the orders past `η`, twice, once in the truncation and once in
`inputRemainder`'s box. Only the second is what [1] reduces.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a zonotope reaches no further than its `ℓ¹` reach. -/
theorem aux_norm_le_absBound_sum {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : ‖x‖ ≤ ∑ j, Z.absBound j := by -- --- PROOF ---
  have habs : ∀ j, (0:ℝ) ≤ Z.absBound j := fun j => by
    rw [Zonotope.absBound]
    positivity
  obtain ⟨β, hβ, hxe⟩ := Zonotope.mem_construct_iff.mp hx
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => habs j)]
  intro i
  rw [Real.norm_eq_abs]
  exact (Zonotope.abs_le_absBound hβ hxe i).trans
    (Finset.single_le_sum (fun j _ => habs j) (Finset.mem_univ i))

/-- The Taylor part of the input solution is a Minkowski sum over the orders, so
each order is free to pick its own input. -/
theorem LinearSys.aux_inputTaylorSum_mem_exists (sys : LinearSys 𝕋 n) (r : ℝ)
    (U : Zonotope (Vec ℝ n)) (η : ℕ) {y : Vec ℝ n}
    (hy : y ∈ (sys.inputTaylorSum (S := 𝒵) r U η).construct) : -- --- STMT ---
    ∃ u : ℕ → Vec ℝ n, (∀ i, u i ∈ U.construct) ∧
      y = ∑ i ∈ Finset.range (η + 1), (sys.inputTerm r i) *ᵥ (u i) := by -- --- PROOF ---
  induction η generalizing y with
  | zero =>
    rw [show sys.inputTaylorSum (S := 𝒵) r U 0 = Zonotope.mtimes (sys.inputTerm r 0) U from rfl,
      ← Zonotope.mtimes_exact] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨fun _ => v, fun _ => hv, by rw [Finset.sum_range_one]⟩
  | succ m ih =>
    rw [show sys.inputTaylorSum (S := 𝒵) r U (m + 1)
        = (sys.inputTaylorSum (S := 𝒵) r U m).plus (Zonotope.mtimes (sys.inputTerm r (m + 1)) U)
        from rfl, ← Zonotope.plus_exact, ← Zonotope.mtimes_exact] at hy
    obtain ⟨y₁, hy₁, _, ⟨v, hv, rfl⟩, rfl⟩ := hy
    obtain ⟨u, hu, rfl⟩ := ih hy₁
    -- the new order takes the fresh input, every earlier one keeps its own
    refine ⟨Function.update u (m + 1) v, fun i => ?_, ?_⟩
    · rcases eq_or_ne i (m + 1) with rfl | hne
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hne]
        exact hu i
    · conv_rhs => rw [Finset.sum_range_succ]
      rw [Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi))]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reverse of `timePointStep_outer`, against the states a *held* input
reaches: what the step computes stays inside `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U`,
widened by `timePointStepError`. -/
theorem LinearSys.timePointStep_subset_constInput_add_error (sys : LinearSys 𝕋 n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ U : Zonotope (Vec ℝ n)) : -- --- STMT ---
    (sys.timePointStep (S := 𝒵) r η X₀ U).construct
      ⊆ ((fun x₀ => exp (r • toRealMat sys.A) *ᵥ x₀) '' X₀.construct
          + (fun v => MatExp.expIntegral (toRealMat sys.A) r *ᵥ v) '' U.construct)
        + Metric.closedBall (0 : Vec ℝ n) (sys.timePointStepError r η U) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set b := MatExp.expRemainderBound (r • A) η with hb
  set B := ∑ j, U.absBound j with hB
  have habs : ∀ j, (0:ℝ) ≤ U.absBound j := fun j => by
    rw [Zonotope.absBound]
    positivity
  have hB0 : (0:ℝ) ≤ B := Finset.sum_nonneg fun j _ => habs j
  have hb0 : (0:ℝ) ≤ b := by
    rw [hb, MatExp.expRemainderBound]
    have h1 : (0:ℝ) < 1 - ‖r • A‖ / ((η : ℝ) + 2) := by linarith
    positivity
  have hnormA : ‖r • A‖ = r * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have hterm : ∀ i : ℕ, sys.inputTerm r i
      = ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i := fun i => by
    rw [LinearSys.inputTerm, hA, div_eq_inv_mul]
  -- what the Minkowski sum over the orders costs, each order free to pick its own input
  have hdep : ∀ u : ℕ → Vec ℝ n, (∀ i, u i ∈ U.construct) →
      ‖∑ i ∈ Finset.range (η + 1), (sys.inputTerm r i) *ᵥ (u i - u 0)‖
        ≤ 2 * B * (r * (Real.exp (r * ‖A‖) - 1)) := by
    intro u hu
    have hzero : (sys.inputTerm r 0) *ᵥ (u 0 - u 0) = 0 := by
      rw [sub_self, Matrix.mulVec_zero]
    rw [Finset.sum_range_succ' (fun i => (sys.inputTerm r i) *ᵥ (u i - u 0)) η, hzero, add_zero]
    have hstep : ∀ i ∈ Finset.range η,
        ‖(sys.inputTerm r (i + 1)) *ᵥ (u (i + 1) - u 0)‖
          ≤ (r * ((Nat.factorial (i + 1) : ℝ)⁻¹ * ‖r • A‖ ^ (i + 1))) * (2 * B) := by
      intro i _
      refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) ?_)
      · rw [hterm]
        exact MatExp.norm_expIntegralTerm_le A hr.le (by omega)
      · calc ‖u (i + 1) - u 0‖ ≤ ‖u (i + 1)‖ + ‖u 0‖ := norm_sub_le _ _
          _ ≤ B + B :=
            add_le_add (aux_norm_le_absBound_sum (hu _)) (aux_norm_le_absBound_sum (hu 0))
          _ = 2 * B := by ring
      · positivity
    -- the orders `1` upwards, summed against the exponential's own
    have hsum : ∑ i ∈ Finset.range η, r * ((Nat.factorial (i + 1) : ℝ)⁻¹ * ‖r • A‖ ^ (i + 1))
        ≤ r * (Real.exp (r * ‖A‖) - 1) := by
      rw [← Finset.mul_sum, ← hnormA]
      exact mul_le_mul_of_nonneg_left (sum_expTail_le (norm_nonneg _) η) hr.le
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right hsum (by positivity)).trans (le_of_eq (by ring))
  -- what truncating the series costs, at one held input
  have htail : ∀ v ∈ U.construct,
      ‖((∑ i ∈ Finset.range (η + 1), sys.inputTerm r i) - MatExp.expIntegral A r) *ᵥ v‖
        ≤ r * b * B := by
    intro v hv
    refine (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul ?_ (aux_norm_le_absBound_sum hv) (norm_nonneg _) (by positivity))
    rw [norm_sub_rev]
    simp only [hterm]
    rw [hb]
    exact MatExp.norm_expIntegral_sub_taylor_le A hr.le η hε
  -- and what the remainder box adds, its center being the origin
  have hbox : ∀ w ∈ (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A r η) U).construct,
      ‖w‖ ≤ (0 + r * b) * B := by
    intro w hw
    have hcen : ∀ i j, |(MatExp.inputRemainder A r η).center i j| ≤ 0 := by
      intro i j
      simp [Interval.center, MatExp.inputRemainder]
    have hrad : ∀ i j, |(MatExp.inputRemainder A r η).radius i j| ≤ r * b := by
      intro i j
      -- the interval is symmetric, so its radius is the bound it was built from
      have hval : (MatExp.inputRemainder A r η).radius i j = r * b := by
        simp [Interval.radius, MatExp.inputRemainder, hb]
        ring
      rw [hval, abs_of_nonneg (by positivity)]
    have hmem := Zonotope.mtimesIntervalMat_subset_closedBall _ U le_rfl
      (by positivity) hcen hrad hw
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  intro y hy
  rw [show sys.timePointStep (S := 𝒵) r η X₀ U
      = (Zonotope.mtimes (exp (r • A)) X₀).plus
          ((sys.inputTaylorSum (S := 𝒵) r U η).plus
            (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A r η) U)) from rfl,
    ← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.mtimes_exact] at hy
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, _, ⟨t, ht, w, hw, rfl⟩, rfl⟩ := hy
  obtain ⟨u, hu, rfl⟩ := sys.aux_inputTaylorSum_mem_exists r U η ht
  -- the exact point is the same initial state under one held input
  refine ⟨exp (r • A) *ᵥ x₀ + MatExp.expIntegral A r *ᵥ u 0,
    Set.add_mem_add (Set.mem_image_of_mem _ hx₀) (Set.mem_image_of_mem _ (hu 0)),
    (∑ i ∈ Finset.range (η + 1), sys.inputTerm r i *ᵥ u i) + w
      - MatExp.expIntegral A r *ᵥ u 0, ?_, by abel_nf⟩
  rw [Metric.mem_closedBall, dist_zero_right, LinearSys.timePointStepError, ← hA, ← hb, ← hB]
  -- the excess, split into the dependency, the truncation and the box
  have hsplit : (∑ i ∈ Finset.range (η + 1), sys.inputTerm r i *ᵥ u i) + w
        - MatExp.expIntegral A r *ᵥ u 0
      = (∑ i ∈ Finset.range (η + 1), sys.inputTerm r i *ᵥ (u i - u 0))
        + (((∑ i ∈ Finset.range (η + 1), sys.inputTerm r i) - MatExp.expIntegral A r) *ᵥ u 0)
        + w := by
    rw [Matrix.sub_mulVec, Matrix.sum_mulVec]
    simp only [Matrix.mulVec_sub]
    rw [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  have hfinal : 2 * B * (r * (Real.exp (r * ‖A‖) - 1)) + (r * b * B + (0 + r * b) * B)
      = 2 * B * r * (Real.exp (r * ‖A‖) - 1 + b) := by ring
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (hdep u hu) (htail (u 0) (hu 0)))) (hbox w hw))).trans ?_
  linarith [hfinal]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

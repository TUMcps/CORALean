import CORALean.HybridDynamics.Operations.AbstractionError
import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.HybridDynamics.Operations.SdcFlow
import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubExpTaylorMemExpRemainderInterval
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.SumTermsMem

/-!
# The abstraction error encloses the difference of a run and the constant flow

[1, Eq. 13] as CORA computes it (`GuardMap.abstractionError`): for `t ∈ [0, tmax]`, `η ≥ 1`,
`x₀ ∈ R₀` and a measurable input `u` with values in `U`, the run
`e^{At}x₀ + ∫₀ᵗ e^{A(t−s)}u(s) ds` of `ẋ = Ax + u` differs from the state-dependent constant
flow `x₀ + (Ax₀ + b)t` of [1, Eq. 3], `b = Θ(th)ξ + Γ*(th)u_c` of [1, Prop. 1] at the centres
`ξ` of `R₀` and `u_c` of `U`, by a point of the set.

Both Taylor series are cut at `η`. The input's orders are averages, `∫₀ᵗ τⁱ u(t − τ) dτ =
tⁱ⁺¹/(i + 1) · wᵢ` with `wᵢ ∈ U` (`integral_pow_smul_mem`), and `wᵢ − u_c ∈ U ⊖ u_c`; the
remainders `R(τ) = e^{Aτ} − ∑ᵢ₌₀^η (Aτ)ⁱ/i!` lie entrywise in `[−W, W]` for `τ ≤ tmax`, so
`R(t)x₀ ∈ Ê R₀` and the integral of `R(τ)u(t − τ)` in `Ê tmax U`, a convex set holding `0`.
`η ≥ 1` because the flow's own `Ax₀t` is the Taylor series' first order. Any `th`: it only
moves `b`, and the error set with it.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point matrix scaled by a point of `[a, b]` lies in the entrywise product
`[lo, hi] * [a, b]`. -/
theorem aux_absErr_smul_mem {lo hi M : Mat ℝ n n} {a b s : ℝ}
    (hM : ∀ j k, lo j k ≤ M j k ∧ M j k ≤ hi j k) (hs : a ≤ s ∧ s ≤ b) :
    s • M ∈ (⟨Matrix.of fun j k => Interval.mulLo (lo j k) (hi j k) a b,
      Matrix.of fun j k => Interval.mulHi (lo j k) (hi j k) a b⟩ :
        Interval (Mat ℝ n n)).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have h := Interval.mul_between_corners (hM j k).1 (hM j k).2 hs.1 hs.2
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm s]
  exact h

/-- A point of the interval matrix applied to a point of the zonotope. -/
theorem aux_absErr_mulVec_mem {IM : Interval (Mat ℝ n n)} {Z : Zonotope (Vec ℝ n)}
    {M : Mat ℝ n n} {v : Vec ℝ n} (hM : M ∈ IM.construct) (hv : v ∈ Z.construct) :
    M *ᵥ v ∈ (Zonotope.mtimesIntervalMat IM Z).construct :=
  Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ hv))

/-- The input integral: its Taylor orders are `tⁱ⁺¹/(i + 1)! Aⁱ wᵢ` with `wᵢ ∈ U`, and what
the cut leaves lies in `Ê tmax U`. -/
theorem aux_absErr_integral (A : Mat ℝ n n) (U : Zonotope (Vec ℝ n)) {tmax t : ℝ}
    (ht : t ∈ Set.Icc 0 tmax) (η : ℕ) {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ U.construct)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t))) :
    ∃ w : ℕ → Vec ℝ n, (∀ i, w i ∈ U.construct) ∧
      (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
        - ∑ i ∈ Finset.range (η + 1), (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i)
      ∈ (Zonotope.mtimesIntervalMat
        ⟨Matrix.of fun j k => Interval.mulLo (-|MatExp.expRemainderMat A tmax η j k|)
            |MatExp.expRemainderMat A tmax η j k| tmax tmax,
          Matrix.of fun j k => Interval.mulHi (-|MatExp.expRemainderMat A tmax η j k|)
            |MatExp.expRemainderMat A tmax η j k| tmax tmax⟩ U).construct := by -- --- PROOF ---
  set W : Mat ℝ n n := fun j k => |MatExp.expRemainderMat A tmax η j k| with hW
  set IM : Interval (Mat ℝ n n) := ⟨Matrix.of fun j k => Interval.mulLo (-W j k) (W j k) tmax tmax,
    Matrix.of fun j k => Interval.mulHi (-W j k) (W j k) tmax tmax⟩ with hIM
  set S : Set (Vec ℝ n) := (Zonotope.mtimesIntervalMat IM U).construct with hS
  have hW0 : ∀ j k, 0 ≤ W j k := fun j k => abs_nonneg _
  -- `S` holds `0`, the zero matrix being a point of `Ê tmax`
  have h0S : (0 : Vec ℝ n) ∈ S := by
    have hz : ∀ j k, (-W) j k ≤ (0 : Mat ℝ n n) j k ∧ (0 : Mat ℝ n n) j k ≤ W j k :=
      fun j k => ⟨neg_nonpos.mpr (hW0 j k), hW0 j k⟩
    have h := aux_absErr_mulVec_mem (Z := U) (v := U.c)
      (aux_absErr_smul_mem (s := tmax) (a := tmax) (b := tmax) hz ⟨le_rfl, le_rfl⟩)
      (Zonotope.centre_mem_construct U)
    simpa using h
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · -- `t = 0`: the integral and every order vanish
    subst h0
    refine ⟨fun _ => U.c, fun _ => Zonotope.centre_mem_construct U, ?_⟩
    simpa using h0S
  -- `t > 0`
  set g : ℝ → Vec ℝ n := fun τ => u (t - τ) with hg
  obtain ⟨C, hC⟩ := (Zonotope.isBounded_construct U).exists_norm_le
  have hint : ∀ (F : ℝ → Vec ℝ n) (K : ℝ),
      AEStronglyMeasurable F (volume.restrict (Set.Ioc 0 t)) →
      (∀ τ ∈ Set.Ioc (0:ℝ) t, ‖F τ‖ ≤ K) → IntervalIntegrable F volume 0 t := by
    intro F K hFm hFb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le]
    exact ⟨hFm, HasFiniteIntegral.restrict_of_bounded (C := K) measure_Ioc_lt_top
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hFb))⟩
  have hgbd : ∀ τ ∈ Set.Ioc (0:ℝ) t, ‖g τ‖ ≤ C := fun τ hτ => hC _ (hu τ hτ)
  -- the substitution `τ = t - s`
  have hsub : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = ∫ τ in (0:ℝ)..t, exp (τ • A) *ᵥ g τ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
      (f := fun τ => exp (τ • A) *ᵥ g τ) t
    simp only [hg, sub_sub_cancel, sub_self, sub_zero] at h
    exact h
  -- the integrand: the Taylor orders to `η` and the remainder `R(τ)`
  have hsplit : ∀ τ : ℝ, exp (τ • A) *ᵥ g τ
      = (∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
        + (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ := by
    intro τ
    rw [← MatExp.expTaylor_smul_mulVec A η τ (g τ), Matrix.sub_mulVec]
    abel
  -- each order is an average of the input, `wᵢ`
  have havg : ∀ i : ℕ, ∃ z ∈ U.construct,
      (∫ τ in (0:ℝ)..t, τ ^ i • g τ) = (t ^ (i + 1) / ((i : ℝ) + 1)) • z := by
    intro i
    obtain ⟨z, hz, hzeq⟩ := integral_pow_smul_mem (Zonotope.convex_construct U)
      (Zonotope.isClosed_construct U) (Zonotope.isBounded_construct U) hpos i hmeas hu
    exact ⟨z, hz, hzeq.symm⟩
  choose w hw hweq using havg
  refine ⟨w, hw, ?_⟩
  -- each order is integrable, bounded by `tⁱ ‖Aⁱ‖ C / i!`
  have hTint : ∀ i ∈ Finset.range (η + 1), IntervalIntegrable
      (fun τ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)) volume 0 t := by
    intro i _
    refine hint _ ((Nat.factorial i : ℝ)⁻¹ * t ^ i * (‖A ^ i‖ * C)) ?_ fun τ hτ => ?_
    · exact (continuous_const.mul (continuous_pow i)).aestronglyMeasurable.smul
        ((mulVecL (A ^ i)).continuous.comp_aestronglyMeasurable hmeas)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hτ.1.le i))]
      refine mul_le_mul ?_ (le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul_of_nonneg_left (hgbd τ hτ) (norm_nonneg _))) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 i) (by positivity)
  -- one order: `Aⁱ/i!` leaves the integral, which is `tⁱ⁺¹/(i + 1) wᵢ`
  have hterm : ∀ i, (∫ τ in (0:ℝ)..t, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
      = (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i) := by
    intro i
    have hgi : IntervalIntegrable (fun τ => τ ^ i • g τ) volume 0 t :=
      hint _ (t ^ i * C) ((continuous_pow i).aestronglyMeasurable.smul hmeas)
        (fun τ hτ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le i)]
          exact mul_le_mul (pow_le_pow_left₀ hτ.1.le hτ.2 i) (hgbd τ hτ) (norm_nonneg _)
            (pow_nonneg hpos.le i))
    -- `Aⁱ` as a continuous linear map commutes with the integral
    have hfun : ∀ τ : ℝ, ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)
        = ((Nat.factorial i : ℝ)⁻¹) • ((mulVecL (A ^ i)) (τ ^ i • g τ)) := by
      intro τ
      rw [map_smul, mul_smul]
      rfl
    have hclm : (∫ τ in (0:ℝ)..t, (mulVecL (A ^ i)) (τ ^ i • g τ))
        = (mulVecL (A ^ i)) (∫ τ in (0:ℝ)..t, τ ^ i • g τ) :=
      ContinuousLinearMap.intervalIntegral_comp_comm _ hgi
    simp only [hfun]
    rw [intervalIntegral.integral_smul, hclm]
    show ((Nat.factorial i : ℝ)⁻¹) • (A ^ i *ᵥ ∫ τ in (0:ℝ)..t, τ ^ i • g τ) = _
    -- `(1/i!) · tⁱ⁺¹/(i + 1) = tⁱ⁺¹/(i + 1)!`
    rw [hweq i, Matrix.mulVec_smul, smul_smul, Nat.factorial_succ]
    congr 1
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    push_cast
    field_simp
  -- the remainder, measured one real entry at a time
  have hgk : ∀ k, AEStronglyMeasurable (fun τ => g τ k) (volume.restrict (Set.Ioc 0 t)) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hmeas)) k
  -- each entry of `R(τ) g(τ)` a finite sum of continuous times measurable
  have hRmeas : AEStronglyMeasurable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
      (volume.restrict (Set.Ioc 0 t)) := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_iff.mpr fun j => ?_
    have hj : ∀ τ : ℝ, ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) j
        = ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := fun _ => rfl
    simp only [hj]
    rw [← aestronglyMeasurable_iff_aemeasurable]
    have heq : (∑ k : Fin n, (fun τ : ℝ =>
          (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k))
        = fun τ : ℝ => ∑ k, (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k * g τ k := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (((MatExp.continuous_expDiff A η).matrix_elem j k).aestronglyMeasurable).mul (hgk k)
  -- and integrable, `R` being continuous on `[0, t]`
  have hRint : IntervalIntegrable
      (fun τ => (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) volume 0 t := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
      (MatExp.continuous_expDiff A η).continuousOn
    refine hint _ (D * C) hRmeas fun τ hτ => ?_
    exact le_trans (Matrix.linfty_opNorm_mulVec _ _)
      (mul_le_mul (hD τ ⟨hτ.1.le, hτ.2⟩) (hgbd τ hτ) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hD 0 ⟨le_refl 0, hpos.le⟩)))
  -- `tmax R(τ)` is a point of `Ê tmax`, so `tmax R(τ) u(t - τ) ∈ S`
  have hpt : ∀ τ ∈ Set.Ioc (0:ℝ) t,
      tmax • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ S := by
    intro τ hτ
    have hR := MatExp.exp_sub_expTaylor_mem_expRemainderInterval A hτ.1.le η
    have hbd : ∀ j k, -W j k ≤ (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k ∧
        (exp (τ • A) - MatExp.expTaylor (τ • A) η) j k ≤ W j k := by
      intro j k
      have h1 := le_trans (hR j k)
        (MatExp.expRemainderMat_mono A hτ.1.le (hτ.2.trans ht.2) η j k)
      exact abs_le.mp (le_trans h1 (le_abs_self _))
    rw [← Matrix.smul_mulVec]
    exact aux_absErr_mulVec_mem (aux_absErr_smul_mem hbd ⟨le_rfl, le_rfl⟩) (hu τ hτ)
  -- the average of `tmax R(τ) u(t − τ)` is in `S`, and so is `1/tmax` times the integral
  have hrem : (∫ τ in (0:ℝ)..t, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ S := by
    have hI := integral_pow_smul_mem (Zonotope.convex_construct _)
      (Zonotope.isClosed_construct _) (Zonotope.isBounded_construct _) hpos 0
      (f := fun τ => tmax • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ))
      (hmeas := hRmeas.fun_const_smul tmax) (hmem := hpt)
    simp only [pow_zero, one_smul, pow_one, Nat.cast_zero, zero_add, div_one,
      intervalIntegral.integral_smul] at hI
    obtain ⟨y, hy, hyeq⟩ := hI
    have hyeq' : t • y = tmax • ∫ τ in (0:ℝ)..t,
        (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ := hyeq
    have htm : 0 < tmax := lt_of_lt_of_le hpos ht.2
    -- `tmax X = t y`, so `X = (t / tmax) y`, a point between `0` and `y`
    have hX : (∫ τ in (0:ℝ)..t, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ)
        = (t / tmax) • y := by
      rw [div_eq_inv_mul, mul_smul, hyeq', smul_smul, inv_mul_cancel₀ htm.ne', one_smul]
    rw [hX]
    exact (Zonotope.convex_construct _).smul_mem_of_zero_mem h0S hy
      ⟨div_nonneg hpos.le htm.le, (div_le_one htm).mpr ht.2⟩
  -- the orders' sum is integrable, so the integral splits
  have hSint : IntervalIntegrable
      (fun τ => ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ))
      volume 0 t := by
    have heq : (∑ i ∈ Finset.range (η + 1),
          (fun τ : ℝ => ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ)))
        = fun τ : ℝ => ∑ i ∈ Finset.range (η + 1),
            ((Nat.factorial i : ℝ)⁻¹ * τ ^ i) • (A ^ i *ᵥ g τ) := by
      funext τ
      simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum _ hTint
  rw [hsub]
  simp only [hsplit]
  rw [intervalIntegral.integral_add hSint hRint, intervalIntegral.integral_finsetSum hTint]
  simp only [hterm, add_sub_cancel_left]
  exact hrem


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13]: `x(t) − y(t) ∈ E` for a run from `x₀ ∈ R₀` with inputs in `U`,
`t ∈ [0, tmax]`, `η ≥ 1`. -/
theorem GuardMap.abstractionError_outer (A : Mat ℝ n n) (U R₀ : Zonotope (Vec ℝ n)) (th : ℝ)
    {tmax t : ℝ} {η : ℕ} (hη : 1 ≤ η) (ht : t ∈ Set.Icc 0 tmax) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ R₀.construct) {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ U.construct)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t))) :
    exp (t • A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
        - GuardMap.sdcFlow A (GuardMap.sdcInput A U.c th η R₀.c) x₀ t
      ∈ (GuardMap.abstractionError A U R₀ th tmax η).construct := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
  obtain ⟨w, hw, hρ⟩ := aux_absErr_integral A U ht (k + 1) hu hmeas
  set ρ : Vec ℝ n := (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
    - ∑ i ∈ Finset.range (k + 1 + 1), (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i)
    with hρdef
  set ξ := R₀.c
  set uc := U.c
  set Mf : ℕ → Mat ℝ n n := fun m => ((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1) with hMf
  -- the three parts of `τ(err₁ ⊕ err₂ ⊕ err₃)`, before the factor `t`
  set v1 : Vec ℝ n := ∑ m ∈ Finset.range k, (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2)) *ᵥ
    (t ^ (m + 1) • x₀ + (-(th ^ (m + 1))) • ξ) with hv1
  set v2 : Vec ℝ n := ∑ m ∈ Finset.range (k + 1), ((t ^ (m + 1) - th ^ (m + 1)) • Mf m) *ᵥ uc
    with hv2
  set v3 : Vec ℝ n := (w 0 - uc) + ∑ m ∈ Finset.range (k + 1), (t ^ (m + 1) • Mf m) *ᵥ
    (w (m + 1) - uc) with hv3
  set R : Mat ℝ n n := exp (t • A) - MatExp.expTaylor (t • A) (k + 1) with hR
  -- the identity: `x(t) − y(t) = t(v₁ + v₂ + v₃) + R(t)x₀ + ρ`
  have hexp : exp (t • A) *ᵥ x₀ = x₀ + t • (A *ᵥ x₀)
      + ∑ m ∈ Finset.range k, (((Nat.factorial (m + 2) : ℝ)⁻¹ * t ^ (m + 2)) • (A ^ (m + 2) *ᵥ x₀))
      + R *ᵥ x₀ := by
    have h := MatExp.expTaylor_smul_mulVec A (k + 1) t x₀
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have h0 : ((Nat.factorial 0 : ℝ)⁻¹ * t ^ 0) • (A ^ 0 *ᵥ x₀) = x₀ := by simp
    have h1 : ((Nat.factorial (0 + 1) : ℝ)⁻¹ * t ^ (0 + 1)) • (A ^ (0 + 1) *ᵥ x₀)
        = t • (A *ᵥ x₀) := by simp
    rw [h0, h1] at h
    have hR' : exp (t • A) *ᵥ x₀ = MatExp.expTaylor (t • A) (k + 1) *ᵥ x₀ + R *ᵥ x₀ := by
      rw [hR, Matrix.sub_mulVec]; abel
    rw [hR', h]
    abel
  -- the input's orders: `t w₀` and the rest, reindexed
  have hsum : ∑ i ∈ Finset.range (k + 1 + 1),
        (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i) = t • w 0
      + ∑ m ∈ Finset.range (k + 1),
          (t ^ (m + 2) / ((Nat.factorial (m + 2)) : ℝ)) • (A ^ (m + 1) *ᵥ w (m + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one, pow_zero,
      Matrix.one_mulVec, show ∀ m : ℕ, m + 1 + 1 = m + 2 from fun m => rfl]
    abel
  have hint : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) = t • w 0
      + ∑ m ∈ Finset.range (k + 1),
          (t ^ (m + 2) / ((Nat.factorial (m + 2)) : ℝ)) • (A ^ (m + 1) *ᵥ w (m + 1)) + ρ := by
    rw [← hsum, hρdef]
    abel
  -- `Θ(th)ξ` and `Γ*(th)u_c` of `b`, reindexed the same way
  have hΘ : (∑ i ∈ Finset.Ico 2 (k + 1 + 1), (th ^ (i - 1) / (i.factorial : ℝ)) • A ^ i) *ᵥ ξ
      = ∑ m ∈ Finset.range k,
          ((th ^ (m + 1) / (Nat.factorial (m + 2) : ℝ)) • (A ^ (m + 2) *ᵥ ξ)) := by
    rw [Matrix.sum_mulVec, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun m _ => ?_
    rw [Matrix.smul_mulVec, show 2 + m = m + 2 by ring, show m + 2 - 1 = m + 1 by omega]
  have hΓ : (∑ i ∈ Finset.range (k + 1 + 1), (th ^ i / ((i + 1).factorial : ℝ)) • A ^ i) *ᵥ uc
      = uc + ∑ m ∈ Finset.range (k + 1),
          ((th ^ (m + 1) / (Nat.factorial (m + 2) : ℝ)) • (A ^ (m + 1) *ᵥ uc)) := by
    rw [Matrix.sum_mulVec, Finset.sum_range_succ']
    simp only [Matrix.smul_mulVec, pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, div_one,
      one_smul, Matrix.one_mulVec]
    abel
  -- order by order, the flow's part cancels against `t v₁` and `t (v₂ + v₃)`
  have EQ1 : ∑ m ∈ Finset.range k, (((Nat.factorial (m + 2) : ℝ)⁻¹ * t ^ (m + 2)) •
        (A ^ (m + 2) *ᵥ x₀)) - t • ∑ m ∈ Finset.range k, ((th ^ (m + 1)
          / (Nat.factorial (m + 2) : ℝ)) • (A ^ (m + 2) *ᵥ ξ)) = t • v1 := by
    rw [hv1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have EQ2 : ∑ m ∈ Finset.range (k + 1),
        (t ^ (m + 2) / ((Nat.factorial (m + 2)) : ℝ)) • (A ^ (m + 1) *ᵥ w (m + 1))
      - t • ∑ m ∈ Finset.range (k + 1), ((th ^ (m + 1) / (Nat.factorial (m + 2) : ℝ)) •
          (A ^ (m + 1) *ᵥ uc))
      = t • (v2 + ∑ m ∈ Finset.range (k + 1), (t ^ (m + 1) • Mf m) *ᵥ (w (m + 1) - uc)) := by
    rw [hv2, ← Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hMf, Matrix.smul_mulVec, Matrix.mulVec_sub]
    module
  -- all of it together
  have hid : exp (t • A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
        - GuardMap.sdcFlow A (GuardMap.sdcInput A U.c th (k + 1) R₀.c) x₀ t
      = (t • (v1 + v2 + v3) + R *ᵥ x₀) + ρ := by
    simp only [GuardMap.sdcFlow, GuardMap.sdcInput]
    rw [hexp, hint, hΘ, hΓ, hv3]
    linear_combination (norm := module) EQ1 + EQ2
  rw [hid]
  -- the memberships, part by part
  simp only [GuardMap.abstractionError, Nat.add_sub_cancel]
  rw [← Zonotope.plus_exact, ← Zonotope.plus_exact]
  have htpow : ∀ m : ℕ, 0 ≤ t ^ m ∧ t ^ m ≤ tmax ^ m := fun m =>
    ⟨pow_nonneg ht.1 m, pow_le_pow_left₀ ht.1 ht.2 m⟩
  have hone : ∀ j k : Fin n, (1 : Mat ℝ n n) j k ≤ (1 : Mat ℝ n n) j k ∧
      (1 : Mat ℝ n n) j k ≤ (1 : Mat ℝ n n) j k := fun _ _ => ⟨le_rfl, le_rfl⟩
  have hself : ∀ (M : Mat ℝ n n) (j k : Fin n), M j k ≤ M j k ∧ M j k ≤ M j k :=
    fun _ _ _ => ⟨le_rfl, le_rfl⟩
  refine Set.add_mem_add (Set.add_mem_add ?_ ?_) hρ
  · -- `t(v₁ + v₂ + v₃) = (t I)(v₁ + v₂ + v₃)`
    have hV : v1 + v2 + v3 ∈ (((Zonotope.sumTerms (fun m =>
        Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2))
          ((Zonotope.mtimesIntervalMat ⟨Matrix.of fun j k => Interval.mulLo
              ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) 0 (tmax ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) 0
              (tmax ^ (m + 1))⟩ R₀).plus (Zonotope.ofPoint (-(th ^ (m + 1)) • ξ)))) k).plus
        (Zonotope.sumTerms (fun m => Zonotope.mtimesIntervalMat
          ⟨Matrix.of fun j k => Interval.mulLo (Mf m j k) (Mf m j k) (-(th ^ (m + 1)))
              (tmax ^ (m + 1) - th ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi (Mf m j k) (Mf m j k) (-(th ^ (m + 1)))
              (tmax ^ (m + 1) - th ^ (m + 1))⟩ (Zonotope.ofPoint uc)) (k + 1))).plus
        (U.recentre.plus (Zonotope.sumTerms (fun m => Zonotope.mtimesIntervalMat
          ⟨Matrix.of fun j k => Interval.mulLo (Mf m j k) (Mf m j k) 0 (tmax ^ (m + 1)),
            Matrix.of fun j k => Interval.mulHi (Mf m j k) (Mf m j k) 0 (tmax ^ (m + 1))⟩
          U.recentre) (k + 1)))).construct := by
      rw [← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.plus_exact]
      refine Set.add_mem_add (Set.add_mem_add ?_ ?_) (Set.add_mem_add
        (Zonotope.sub_centre_mem_recentre (hw 0)) ?_)
      · -- `err₁`: `(Aⁱ/i!)(tⁱ⁻¹x₀ − thⁱ⁻¹ξ)`, `tⁱ⁻¹ ∈ [0, tmaxⁱ⁻¹]`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        rw [← Zonotope.mtimes_exact, ← Zonotope.plus_exact]
        refine ⟨_, Set.add_mem_add ?_ (Zonotope.mem_ofPoint _), rfl⟩
        rw [show t ^ (m + 1) • x₀ = (t ^ (m + 1) • (1 : Mat ℝ n n)) *ᵥ x₀ by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]]
        exact aux_absErr_mulVec_mem (aux_absErr_smul_mem hone (htpow (m + 1))) hx₀
      · -- `err₂`: `((tⁱ − thⁱ) Aⁱ/(i+1)!) u_c`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        refine aux_absErr_mulVec_mem (aux_absErr_smul_mem (hself (Mf m)) ⟨?_, ?_⟩)
          (Zonotope.mem_ofPoint _)
        · linarith [(htpow (m + 1)).1]
        · linarith [(htpow (m + 1)).2]
      · -- `err₃`: `(tⁱ Aⁱ/(i+1)!)(wᵢ − u_c)`
        refine Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_
        exact aux_absErr_mulVec_mem (aux_absErr_smul_mem (hself (Mf m)) (htpow (m + 1)))
          (Zonotope.sub_centre_mem_recentre (hw (m + 1)))
    rw [show t • (v1 + v2 + v3) = (t • (1 : Mat ℝ n n)) *ᵥ (v1 + v2 + v3) by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]]
    exact aux_absErr_mulVec_mem (aux_absErr_smul_mem hone ⟨ht.1, by simpa using ht.2⟩) hV
  · -- `R(t) ∈ Ê`
    have hRb := MatExp.exp_sub_expTaylor_mem_expRemainderInterval A ht.1 (k + 1)
    refine aux_absErr_mulVec_mem (Interval.mem_mat_iff.mpr fun j k' => ?_) hx₀
    have h1 := le_trans (hRb j k') (MatExp.expRemainderMat_mono A ht.1 ht.2 (k + 1) j k')
    exact abs_le.mp (le_trans h1 (le_abs_self _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

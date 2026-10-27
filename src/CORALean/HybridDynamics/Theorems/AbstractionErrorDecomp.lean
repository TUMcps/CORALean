module

public import CORALean.HybridDynamics.Definitions.SdcInput
public import CORALean.HybridDynamics.Operations.SdcFlow
public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec

@[expose] public section

/-!
# The difference of a run and the constant flow, order by order

The identity behind [1, Eq. 13], every membership left to the caller: for `t ∈ [0, tmax]`,
`η = k + 1` and a measurable input `u` in a convex closed bounded nonempty `U`, the run of
`ẋ = Ax + u` minus the state-dependent constant flow `x₀ + (Ax₀ + b)t`, `b = Θ(th)ξ + Γ*(th)u_c` of
[1, Prop. 1], is `t(v₁ + v₂ + v₃) + R x₀ + ρ` with `v₁, v₂, v₃` sums over the orders, `wᵢ ∈ U`, `R`
within `W` entrywise and `ρ` in a convex closed bounded `S ∋ 0`. CORA's sets of
`aux_abstractionError` [2] hold each part; `GuardMap.abstractionError_outer` and the float layer's
read the memberships off their own sets. The input's orders are averages (`integral_pow_smul_mem`).

## Inputs
* `A` – flow matrix
* `Us` – input set
* `S` – remainder set
* `uc` – center of the input set
* `ξ` – center of the initial set
* `th` – expansion time
* `tmax` – final time
* `t` – time
* `k` – Taylor order minus one
* `W` – entrywise bound on the remainders
* `x₀` – initial state
* `u` – input trajectory

## Hypotheses
* `hUc` – input set convex
* `hUcl` – input set closed
* `hUb` – input set bounded
* `hUn` – input set nonempty
* `hSc` – remainder set convex
* `hScl` – remainder set closed
* `hSb` – remainder set bounded
* `hS0` – remainder set contains zero
* `ht` – time within the horizon
* `hW` – remainder bounded entrywise by the matrix
* `hS` – matrix products of the input stay in the remainder set
* `hu` – input stays in its set
* `hmeas` – input measurable

## Conclusion
* difference of run and flow splits into order terms and a remainder in `S`

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
* [2] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_abstractionError`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The input integral: its Taylor orders are `tⁱ⁺¹/(i + 1)! Aⁱ wᵢ` with `wᵢ ∈ U`, and what
the cut leaves lies in any convex closed bounded `S ∋ 0` that holds `tmax M v` for every `M`
within `W` entrywise and `v ∈ U`, `W` bounding the remainders on `[0, tmax]`. -/
private theorem aux_absErrDecomp_integral (A : Mat ℝ n n) {Us S : Set (Vec ℝ n)} (hUc : Convex ℝ Us)
    (hUcl : IsClosed Us) (hUb : Bornology.IsBounded Us) (hUn : Us.Nonempty) (hSc : Convex ℝ S)
    (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hS0 : (0 : Vec ℝ n) ∈ S) {tmax t : ℝ}
    (ht : t ∈ Set.Icc 0 tmax) (η : ℕ) (W : Mat ℝ n n)
    (hW : ∀ τ ∈ Set.Icc 0 tmax, ∀ j k, |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k| ≤ W j k)
    (hS : ∀ M : Mat ℝ n n, (∀ j k, |M j k| ≤ W j k) → ∀ v ∈ Us, tmax • (M *ᵥ v) ∈ S)
    {u : ℝ → Vec ℝ n} (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ Us)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t)))
    : -- --- CONCL ---
    ∃ w : ℕ → Vec ℝ n, (∀ i, w i ∈ Us) ∧
      (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
        - ∑ i ∈ Finset.range (η + 1), (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i)
      ∈ S := by -- --- PROOF ---
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · -- `t = 0`: the integral and every order vanish
    subst h0
    obtain ⟨w₀, hw₀⟩ := hUn
    refine ⟨fun _ => w₀, fun _ => hw₀, ?_⟩
    simpa using hS0
  -- `t > 0`
  set g : ℝ → Vec ℝ n := fun τ => u (t - τ) with hg
  obtain ⟨C, hC⟩ := hUb.exists_norm_le
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
  have havg : ∀ i : ℕ, ∃ z ∈ Us,
      (∫ τ in (0:ℝ)..t, τ ^ i • g τ) = (t ^ (i + 1) / ((i : ℝ) + 1)) • z := by
    intro i
    obtain ⟨z, hz, hzeq⟩ := integral_pow_smul_mem hUc hUcl hUb hpos i hmeas hu
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
      tmax • ((exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ S := fun τ hτ =>
    hS _ (hW τ ⟨hτ.1.le, hτ.2.trans ht.2⟩) _ (hu τ hτ)
  -- the average of `tmax R(τ) u(t − τ)` is in `S`, and so is `1/tmax` times the integral
  have hrem : (∫ τ in (0:ℝ)..t, (exp (τ • A) - MatExp.expTaylor (τ • A) η) *ᵥ g τ) ∈ S := by
    have hI := integral_pow_smul_mem hSc hScl hSb hpos 0
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
    exact hSc.smul_mem_of_zero_mem hS0 hy
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

/-- [1, Eq. 13]'s identity: `x(t) − y(t) = t(v₁ + v₂ + v₃) + R x₀ + ρ`. -/
theorem GuardMap.abstractionError_decomp (A : Mat ℝ n n) {Us S : Set (Vec ℝ n)}
    (hUc : Convex ℝ Us) (hUcl : IsClosed Us) (hUb : Bornology.IsBounded Us) (hUn : Us.Nonempty)
    (hSc : Convex ℝ S) (hScl : IsClosed S) (hSb : Bornology.IsBounded S)
    (hS0 : (0 : Vec ℝ n) ∈ S) (uc ξ : Vec ℝ n) (th : ℝ) {tmax t : ℝ} {k : ℕ}
    (ht : t ∈ Set.Icc 0 tmax) (W : Mat ℝ n n)
    (hW : ∀ τ ∈ Set.Icc 0 tmax, ∀ j l,
      |(exp (τ • A) - MatExp.expTaylor (τ • A) (k + 1)) j l| ≤ W j l)
    (hS : ∀ M : Mat ℝ n n, (∀ j l, |M j l| ≤ W j l) → ∀ v ∈ Us, tmax • (M *ᵥ v) ∈ S)
    (x₀ : Vec ℝ n) {u : ℝ → Vec ℝ n} (hu : ∀ τ ∈ Set.Ioc (0:ℝ) t, u (t - τ) ∈ Us)
    (hmeas : AEStronglyMeasurable (fun τ => u (t - τ)) (volume.restrict (Set.Ioc 0 t)))
    : -- --- CONCL ---
    ∃ w : ℕ → Vec ℝ n, (∀ i, w i ∈ Us) ∧ ∃ ρ ∈ S,
      exp (t • A) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
          - GuardMap.sdcFlow A (GuardMap.sdcInput A uc th (k + 1) ξ) x₀ t
        = t • ((∑ m ∈ Finset.range k, (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2)) *ᵥ
              (t ^ (m + 1) • x₀ + (-(th ^ (m + 1))) • ξ))
            + (∑ m ∈ Finset.range (k + 1), ((t ^ (m + 1) - th ^ (m + 1)) •
              (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1))) *ᵥ uc)
            + ((w 0 - uc) + ∑ m ∈ Finset.range (k + 1), (t ^ (m + 1) •
              (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1))) *ᵥ (w (m + 1) - uc)))
          + (exp (t • A) - MatExp.expTaylor (t • A) (k + 1)) *ᵥ x₀ + ρ := by -- --- PROOF ---
  obtain ⟨w, hw, hρ⟩ := aux_absErrDecomp_integral A hUc hUcl hUb hUn hSc hScl hSb hS0 ht (k + 1)
    W hW hS hu hmeas
  set ρ : Vec ℝ n := (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
    - ∑ i ∈ Finset.range (k + 1 + 1), (t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ w i)
    with hρdef
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
        - GuardMap.sdcFlow A (GuardMap.sdcInput A uc th (k + 1) ξ) x₀ t
      = (t • (v1 + v2 + v3) + R *ᵥ x₀) + ρ := by
    simp only [GuardMap.sdcFlow, GuardMap.sdcInput]
    rw [hexp, hint, hΘ, hΓ, hv3]
    linear_combination (norm := module) EQ1 + EQ2
  exact ⟨w, hw, ρ, hρ, hid⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

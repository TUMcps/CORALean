module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# The closed form satisfies the raw integral equation, for any bounded input

`closedForm` solves `IsTrajectory.flow` at every `τ`, for `u` merely
bounded and measurable — no continuity, so a piecewise-constant input is
covered. It gets there from nothing but the formula itself, by a Duhamel
swap: `∫₀ᵗ∫₀ᵖ = ∫₀ᵗ∫_σ^t` over the triangle `0 ≤ σ ≤ ρ ≤ τ`, folded into a
rectangle by an indicator so `intervalIntegral_intervalIntegral_swap` applies.

## Inputs
* `sys` – linear system
* `x0` – initial point
* `U` – input set
* `t` – time
* `u` – input signal
* `τ` – point of the window

## Hypotheses
* `ht` – time nonnegative
* `hU` – input set bounded
* `hu` – input values lie in the set on the window
* `hmeas` – input measurable on the window
* `hτ` – point lies within the window

## Conclusion
* the closed form satisfies the integral equation at the point
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix moving with an everywhere-derivative carries that derivative
through `*ᵥ` at any fixed vector, `mulVecL` turning the product rule's other
term into `0`. -/
private theorem aux_hasDerivAt_mulVec_const {M : ℝ → Mat ℝ n n} {M' : Mat ℝ n n} {ρ : ℝ}
    (hM : HasDerivAt M M' ρ) (v : Vec ℝ n) : -- --- CONCL ---
    HasDerivAt (fun r => M r *ᵥ v) (M' *ᵥ v) ρ := by -- --- PROOF ---
  have hC : HasDerivAt (fun r => mulVecL (M r)) (mulVecL M') ρ :=
    (ContinuousLinearMap.hasFDerivAt mulVecL).comp_hasDerivAt ρ hM
  have hCv : HasDerivAt (fun r => (mulVecL (M r)) v) ((mulVecL M') v) ρ :=
    (ContinuousLinearMap.apply ℝ (Vec ℝ n) v).hasFDerivAt.comp_hasDerivAt ρ hC
  exact hCv

/-- `d/dρ [exp((ρ-σ)A) v] = A e^{(ρ-σ)A} v`, at a fixed vector `v` — the shift
absorbed by `exp((r-σ)A) = exp(rA)e^{-σA}` before ever differentiating, every
rewrite through `*ᵥ` rather than raw matrix multiplication. -/
private theorem aux_hasDerivAt_expSub_mulVec (A : Mat ℝ n n) (σ : ℝ) (v : Vec ℝ n)
    (ρ : ℝ) : -- --- CONCL ---
    HasDerivAt (fun r : ℝ => exp ((r - σ) • A) *ᵥ v)
      (A *ᵥ (exp ((ρ - σ) • A) *ᵥ v)) ρ := by -- --- PROOF ---
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := fun c d => by
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]; exact (exp_add_of_commute hc).symm
  have heq : (fun r : ℝ => exp ((r - σ) • A) *ᵥ v)
      = fun r => exp (r • A) *ᵥ (exp ((-σ) • A) *ᵥ v) := by
    funext r
    simp only [Matrix.mulVec_mulVec, hmul, sub_eq_add_neg]
  rw [heq]
  have h2 := aux_hasDerivAt_mulVec_const (hasDerivAt_exp_smul_const' A ρ) (exp ((-σ) • A) *ᵥ v)
  have hval : (A * exp (ρ • A)) *ᵥ (exp ((-σ) • A) *ᵥ v) = A *ᵥ (exp ((ρ - σ) • A) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hmul, sub_eq_add_neg]
  exact hval ▸ h2

/-- A continuous matrix-valued factor applied to a measurable vector-valued
one, entry by entry — the domain generalised from `ℝ` to any measurable space,
for the product-measure rectangle the Duhamel swap runs over. -/
private theorem aux_aestronglyMeasurable_mulVec2 {γ : Type} [MeasurableSpace γ] [TopologicalSpace γ]
    [OpensMeasurableSpace γ] {M : γ → Mat ℝ n n} {v : γ → Vec ℝ n} {μ : Measure γ}
    (hM : Continuous M) (hv : AEStronglyMeasurable v μ) : -- --- CONCL ---
    AEStronglyMeasurable (fun s => M s *ᵥ v s) μ := by -- --- PROOF ---
  have hvk : ∀ k, AEStronglyMeasurable (fun s => v s k) μ := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hv)) k
  rw [aestronglyMeasurable_iff_aemeasurable]
  refine aemeasurable_pi_iff.mpr fun j => ?_
  have hj : ∀ s : γ, (M s *ᵥ v s) j = ∑ k, M s j k * v s k := fun _ => rfl
  simp only [hj]
  rw [← aestronglyMeasurable_iff_aemeasurable]
  have heq : (∑ k : Fin n, (fun s : γ => M s j k * v s k))
      = fun s : γ => ∑ k, M s j k * v s k := by
    funext s; simp only [Finset.sum_apply]
  rw [← heq]
  exact Finset.aestronglyMeasurable_sum _ fun k _ =>
    ((hM.matrix_elem j k).aestronglyMeasurable).mul (hvk k)

/-- The Duhamel identity: what `A` applied to the input-integral part of
`closedForm`, plus the input itself, integrates to — proved by folding the
triangle `0 ≤ σ ≤ ρ ≤ τ` into a rectangle and swapping the iterated integral. -/
private theorem aux_duhamel_swap (sys : LinearSys 𝕋 n) {U : S n} {t : ℝ} (_ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0:ℝ) t) : -- --- CONCL ---
    (∫ ρ in (0:ℝ)..τ,
        toRealMat sys.A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • toRealMat sys.A) *ᵥ u s))
      + ∫ ρ in (0:ℝ)..τ, u ρ
      = ∫ s in (0:ℝ)..τ, exp ((τ - s) • toRealMat sys.A) *ᵥ u s := by -- --- PROOF ---
  -- `F` is the un-indicated Duhamel kernel, `G` its restriction to the triangle `σ ≤ ρ`
  set A := toRealMat sys.A
  obtain ⟨hτ0, hτt⟩ := hτ
  obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
  have hu' : ∀ s ∈ Set.Icc (0:ℝ) τ, u s ∈ construct U := fun s hs =>
    hu s (Set.Icc_subset_Icc_right hτt hs)
  have hmeas' : AEStronglyMeasurable u (volume.restrict (Set.Icc (0:ℝ) τ)) :=
    hmeas.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hτt) le_rfl)
  set F : ℝ → ℝ → Vec ℝ n := fun ρ σ => A *ᵥ (exp ((ρ - σ) • A) *ᵥ u σ) with hFdef
  set G : ℝ → ℝ → Vec ℝ n := fun ρ σ => if σ ≤ ρ then F ρ σ else 0 with hGdef
  have hFcont : ∀ σ : ℝ, Continuous fun ρ => F ρ σ := by
    intro σ
    have h1 : Continuous fun ρ : ℝ => mulVecL (exp ((ρ - σ) • A)) :=
      mulVecL.continuous.comp
        (exp_continuous.comp ((continuous_id.sub continuous_const).smul continuous_const))
    exact (mulVecL A).continuous.comp (h1.clm_apply continuous_const)
  -- the triangle folded into a rectangle by an indicator on `σ ≤ ρ`
  have hclaimA : ∀ ρ ∈ Set.Icc (0:ℝ) τ, ∫ σ in (0:ℝ)..τ, G ρ σ = ∫ σ in (0:ℝ)..ρ, F ρ σ := by
    intro ρ hρ
    have heq : (fun σ => G ρ σ) = Set.indicator {x | x ≤ ρ} (F ρ) := by
      funext σ; simp only [hGdef, Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq]
    exact intervalIntegral.integral_indicator ⟨hρ.1, hρ.2⟩
  have hclaimB : ∀ σ ∈ Set.Icc (0:ℝ) τ, ∫ ρ in (0:ℝ)..τ, G ρ σ = ∫ ρ in σ..τ, F ρ σ := by
    intro σ hσ
    have hzero : ∫ ρ in (0:ℝ)..σ, G ρ σ = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [Measure.ae_ne volume σ] with ρ hρne hρ
      rw [Set.uIoc_of_le hσ.1] at hρ
      simp only [hGdef]
      exact if_neg (not_le.mpr (lt_of_le_of_ne hρ.2 hρne))
    -- the split point `σ` itself is null, so `G` agrees with `F` past it regardless
    have hsecond : ∫ ρ in σ..τ, G ρ σ = ∫ ρ in σ..τ, F ρ σ := by
      apply intervalIntegral.integral_congr
      intro ρ hρ
      rw [Set.uIcc_of_le hσ.2] at hρ
      simp only [hGdef]
      exact if_pos hρ.1
    have hGint1 : IntervalIntegrable (fun ρ => G ρ σ) volume 0 σ := by
      refine IntervalIntegrable.congr_uIoo (f := fun _ => (0 : Vec ℝ n))
        intervalIntegrable_const fun ρ hρ => ?_
      rw [Set.uIoo_of_le hσ.1] at hρ
      simp only [hGdef]
      exact (if_neg (not_le.mpr hρ.2)).symm
    have hGint2 : IntervalIntegrable (fun ρ => G ρ σ) volume σ τ := by
      refine ((hFcont σ).intervalIntegrable σ τ).congr fun ρ hρ => ?_
      rw [Set.uIoc_of_le hσ.2] at hρ
      simp only [hGdef]
      exact (if_pos hρ.1.le).symm
    rw [← intervalIntegral.integral_add_adjacent_intervals hGint1 hGint2, hzero, zero_add, hsecond]
  -- `G`'s joint measurability and boundedness on the rectangle
  have hMcont : Continuous fun p : ℝ × ℝ => exp ((p.1 - p.2) • A) :=
    exp_continuous.comp ((continuous_fst.sub continuous_snd).smul continuous_const)
  -- the product of two copies of the restricted Lebesgue measure
  set μ₂ := (volume.restrict (Set.Ioc (0:ℝ) τ)).prod (volume.restrict (Set.Ioc (0:ℝ) τ)) with hμ₂
  have hGmeas : AEStronglyMeasurable (Function.uncurry G) μ₂ := by
    have hv : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.2) μ₂ :=
      AEStronglyMeasurable.comp_snd
        (hmeas'.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
    -- `A` and the shifted exponential, then `u ∘ snd`, combined entry by entry
    have hFm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) μ₂ :=
      aux_aestronglyMeasurable_mulVec2 (continuous_const : Continuous fun _ : ℝ × ℝ => A)
        (aux_aestronglyMeasurable_mulVec2 hMcont hv)
    have hGeq : Function.uncurry G
        = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => F p.1 p.2) := by
      funext p
      show G p.1 p.2 = _
      rw [hGdef]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hGeq]
    exact hFm.indicator (measurableSet_le measurable_snd measurable_fst)
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := -τ) (b := τ)).exists_bound_of_continuousOn
    (show Continuous fun d : ℝ => exp (d • A) from
      exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
  have hCE0 : (0:ℝ) ≤ CE := le_trans (norm_nonneg _) (hCE 0 ⟨by linarith, by linarith⟩)
  have hCu0 : (0:ℝ) ≤ Cu := le_trans (norm_nonneg _) (hCu _ (hu' 0 ⟨le_refl 0, hτ0⟩))
  -- `‖A‖ CE Cu` bounds `F` on the rectangle, `CE` from `exp` over the compact range of `ρ - σ`
  have hFbound : ∀ ρ σ, ρ ∈ Set.Icc (0:ℝ) τ → σ ∈ Set.Icc (0:ℝ) τ → ‖F ρ σ‖ ≤ ‖A‖ * CE * Cu := by
    intro ρ σ hρ hσ
    calc ‖F ρ σ‖ ≤ ‖A‖ * ‖exp ((ρ - σ) • A) *ᵥ u σ‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ‖A‖ * (‖exp ((ρ - σ) • A)‖ * ‖u σ‖) :=
          mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (norm_nonneg _)
      _ ≤ ‖A‖ * (CE * Cu) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hCu _ (hu' σ hσ)) (norm_nonneg _) hCE0)
            (norm_nonneg _)
          exact hCE _ ⟨by linarith [hρ.1, hσ.2], by linarith [hρ.2, hσ.1]⟩
      _ = ‖A‖ * CE * Cu := (mul_assoc _ _ _).symm
  -- the rectangle has finite measure, and `G` is bounded on it by `hFbound`
  have hGint : IntegrableOn (Function.uncurry G) (Set.uIoc (0:ℝ) τ ×ˢ Set.uIoc (0:ℝ) τ) := by
    rw [Set.uIoc_of_le hτ0]
    have hGmeas' : AEStronglyMeasurable (Function.uncurry G)
        (volume.restrict (Set.Ioc (0:ℝ) τ ×ˢ Set.Ioc (0:ℝ) τ)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact hGmeas
    have hfin : volume (Set.Ioc (0:ℝ) τ ×ˢ Set.Ioc (0:ℝ) τ) < ⊤ := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
    refine ⟨hGmeas', HasFiniteIntegral.restrict_of_bounded (C := ‖A‖ * CE * Cu) hfin ?_⟩
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
      (Filter.Eventually.of_forall fun p hp => ?_)
    show ‖G p.1 p.2‖ ≤ ‖A‖ * CE * Cu
    by_cases hif : p.2 ≤ p.1
    · rw [hGdef]; simp only [if_pos hif]
      exact hFbound p.1 p.2 ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩
    · rw [hGdef]; simp only [if_neg hif]
      simpa using mul_nonneg (mul_nonneg (norm_nonneg A) hCE0) hCu0
  have hswap : ∫ ρ in (0:ℝ)..τ, ∫ σ in (0:ℝ)..τ, G ρ σ = ∫ σ in (0:ℝ)..τ, ∫ ρ in (0:ℝ)..τ, G ρ σ :=
    intervalIntegral_intervalIntegral_swap hGint
  -- pushing `A` inside the input-integral part of `closedForm`
  have hpush : ∀ ρ ∈ Set.Icc (0:ℝ) τ,
      A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s) = ∫ σ in (0:ℝ)..ρ, F ρ σ := by
    intro ρ hρ
    have hint : IntervalIntegrable (fun s => exp ((ρ - s) • A) *ᵥ u s) volume 0 ρ :=
      intervalIntegrable_expSub_mulVec hρ.1 hU
        (fun s hs => hu' s (Set.Icc_subset_Icc_right hρ.2 hs))
        (hmeas'.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hρ.2) le_rfl))
    exact (ContinuousLinearMap.intervalIntegral_comp_comm (mulVecL A) hint).symm
  -- the fundamental theorem, on `F`'s own everywhere-derivative in `ρ`
  have hinner : ∀ σ ∈ Set.Icc (0:ℝ) τ, ∫ ρ in σ..τ, F ρ σ = exp ((τ - σ) • A) *ᵥ u σ - u σ := by
    intro σ hσ
    have hderiv : ∀ ρ : ℝ, HasDerivAt (fun r => exp ((r - σ) • A) *ᵥ u σ) (F ρ σ) ρ :=
      fun ρ => aux_hasDerivAt_expSub_mulVec A σ (u σ) ρ
    have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r => exp ((r - σ) • A) *ᵥ u σ) (fun ρ _ => hderiv ρ)
      ((hFcont σ).intervalIntegrable σ τ)
    simpa using hres
  have huint : IntervalIntegrable u volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0]
    refine ⟨hmeas'.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl),
      HasFiniteIntegral.restrict_of_bounded (C := Cu) measure_Ioc_lt_top ?_⟩
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun s hs => hCu _ (hu' s ⟨hs.1.le, hs.2⟩))
  have hexp_int : IntervalIntegrable (fun σ => exp ((τ - σ) • A) *ᵥ u σ) volume 0 τ :=
    intervalIntegrable_expSub_mulVec hτ0 hU hu' hmeas'
  -- assemble: the swap turns the triangle sum into `hinner`'s telescoping difference
  calc (∫ ρ in (0:ℝ)..τ, A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s)) + ∫ ρ in (0:ℝ)..τ, u ρ
      = (∫ ρ in (0:ℝ)..τ, ∫ σ in (0:ℝ)..ρ, F ρ σ) + ∫ ρ in (0:ℝ)..τ, u ρ := by
        rw [intervalIntegral.integral_congr (g := fun ρ => ∫ σ in (0:ℝ)..ρ, F ρ σ)]
        intro ρ hρ
        rw [Set.uIcc_of_le hτ0] at hρ
        exact hpush ρ hρ
    _ = (∫ ρ in (0:ℝ)..τ, ∫ σ in (0:ℝ)..τ, G ρ σ) + ∫ ρ in (0:ℝ)..τ, u ρ := by
        rw [intervalIntegral.integral_congr (g := fun ρ => ∫ σ in (0:ℝ)..τ, G ρ σ)]
        intro ρ hρ
        rw [Set.uIcc_of_le hτ0] at hρ
        exact (hclaimA ρ hρ).symm
    -- Fubini, then folding the rectangle back into the triangle from the other side
    _ = (∫ σ in (0:ℝ)..τ, ∫ ρ in (0:ℝ)..τ, G ρ σ) + ∫ ρ in (0:ℝ)..τ, u ρ := by rw [hswap]
    _ = (∫ σ in (0:ℝ)..τ, ∫ ρ in σ..τ, F ρ σ) + ∫ ρ in (0:ℝ)..τ, u ρ := by
        rw [intervalIntegral.integral_congr (g := fun σ => ∫ ρ in σ..τ, F ρ σ)]
        intro σ hσ
        rw [Set.uIcc_of_le hτ0] at hσ
        exact hclaimB σ hσ
    _ = (∫ σ in (0:ℝ)..τ, (exp ((τ - σ) • A) *ᵥ u σ - u σ)) + ∫ ρ in (0:ℝ)..τ, u ρ := by
        rw [intervalIntegral.integral_congr (g := fun σ => exp ((τ - σ) • A) *ᵥ u σ - u σ)]
        intro σ hσ
        rw [Set.uIcc_of_le hτ0] at hσ
        exact hinner σ hσ
    _ = ((∫ σ in (0:ℝ)..τ, exp ((τ - σ) • A) *ᵥ u σ) - ∫ σ in (0:ℝ)..τ, u σ)
        + ∫ ρ in (0:ℝ)..τ, u ρ := by
        rw [intervalIntegral.integral_sub hexp_int huint]
    _ = ∫ s in (0:ℝ)..τ, exp ((τ - s) • toRealMat sys.A) *ᵥ u s := by
        rw [sub_add_cancel]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The closed form satisfies the raw integral equation, at every point of the
window, for `u` merely bounded and measurable there. -/
theorem LinearSys.closedForm_flow (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) {U : S n} {t : ℝ}
    (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0:ℝ) t) : -- --- CONCL ---
    sys.closedForm x0 u τ
      = sys.closedForm x0 u 0
        + ∫ ρ in (0:ℝ)..τ, (toRealMat sys.A *ᵥ sys.closedForm x0 u ρ + u ρ) := by -- --- PROOF ---
  set A := toRealMat sys.A with hAeq
  obtain ⟨hτ0, hτt⟩ := hτ
  have hu' : ∀ s ∈ Set.Icc (0:ℝ) τ, u s ∈ construct U := fun s hs =>
    hu s (Set.Icc_subset_Icc_right hτt hs)
  have hmeas' : AEStronglyMeasurable u (volume.restrict (Set.Icc (0:ℝ) τ)) :=
    hmeas.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hτt) le_rfl)
  have hx0 : sys.closedForm x0 u 0 = x0 := sys.closedForm_zero x0 u
  -- the homogeneous part, by the fundamental theorem on an everywhere derivative
  have hderiv1 : ∀ ρ : ℝ,
      HasDerivAt (fun r : ℝ => exp (r • A) *ᵥ x0) (A *ᵥ (exp (ρ • A) *ᵥ x0)) ρ :=
    fun ρ => by simpa using aux_hasDerivAt_expSub_mulVec A 0 x0 ρ
  have hMcont : Continuous fun ρ : ℝ => mulVecL (exp (ρ • A)) :=
    mulVecL.continuous.comp (exp_continuous.comp (continuous_id.smul continuous_const))
  have hf'cont : Continuous fun ρ : ℝ => A *ᵥ (exp (ρ • A) *ᵥ x0) :=
    (mulVecL A).continuous.comp (hMcont.clm_apply continuous_const)
  have hpiece1 : ∫ ρ in (0:ℝ)..τ, A *ᵥ (exp (ρ • A) *ᵥ x0) = exp (τ • A) *ᵥ x0 - x0 := by
    have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ => hderiv1 ρ)
      (hf'cont.intervalIntegrable 0 τ)
    simpa using hres
  -- `A *ᵥ closedForm` is continuous, hence integrable, and splits as piece 1 plus piece 2
  have hcc : ContinuousOn (sys.closedForm x0 u) (Set.Icc 0 t) :=
    sys.closedForm_continuousOn x0 ht hU hu hmeas
  have hAcc : ContinuousOn (fun ρ => A *ᵥ sys.closedForm x0 u ρ) (Set.Icc (0:ℝ) τ) :=
    ((mulVecL A).continuous.comp_continuousOn hcc).mono (Set.Icc_subset_Icc_right hτt)
  have hAcc' : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm x0 u ρ) volume 0 τ := by
    rw [← Set.uIcc_of_le hτ0] at hAcc
    exact hAcc.intervalIntegrable
  -- piece 2 is the whole minus piece 1, both already known integrable
  have hpiece2 : IntervalIntegrable
      (fun ρ => A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s)) volume 0 τ := by
    have heqfun : (fun ρ => A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s))
        = (fun ρ => A *ᵥ sys.closedForm x0 u ρ) - fun ρ => A *ᵥ (exp (ρ • A) *ᵥ x0) := by
      funext ρ
      show _ = A *ᵥ sys.closedForm x0 u ρ - A *ᵥ (exp (ρ • A) *ᵥ x0)
      show _ = A *ᵥ (exp (ρ • A) *ᵥ x0 + ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s)
        - A *ᵥ (exp (ρ • A) *ᵥ x0)
      rw [Matrix.mulVec_add]
      abel
    rw [heqfun]
    exact hAcc'.sub (hf'cont.intervalIntegrable 0 τ)
  have huint : IntervalIntegrable u volume 0 τ := by
    obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0]
    refine ⟨hmeas'.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl),
      HasFiniteIntegral.restrict_of_bounded (C := Cu) measure_Ioc_lt_top ?_⟩
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun s hs => hCu _ (hu' s ⟨hs.1.le, hs.2⟩))
  -- Duhamel turns piece 2 plus the input's own integral into the target's second term
  have hduhamel := aux_duhamel_swap sys ht hU hu hmeas ⟨hτ0, hτt⟩
  rw [← hAeq] at hduhamel
  rw [hx0]
  show exp (τ • A) *ᵥ x0 + ∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ u s
    = x0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm x0 u ρ + u ρ)
  have heqcongr : (∫ ρ in (0:ℝ)..τ, A *ᵥ sys.closedForm x0 u ρ)
      = ∫ ρ in (0:ℝ)..τ,
          (A *ᵥ (exp (ρ • A) *ᵥ x0) + A *ᵥ (∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s)) := by
    apply intervalIntegral.integral_congr
    intro ρ _
    show A *ᵥ sys.closedForm x0 u ρ = _
    show A *ᵥ (exp (ρ • A) *ᵥ x0 + ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s) = _
    rw [Matrix.mulVec_add]
  rw [intervalIntegral.integral_add hAcc' huint, heqcongr,
    intervalIntegral.integral_add (hf'cont.intervalIntegrable 0 τ) hpiece2, hpiece1]
  generalize hP : (∫ ρ in (0:ℝ)..τ, A *ᵥ ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s) = P at *
  generalize hUi : (∫ ρ in (0:ℝ)..τ, u ρ) = Ui at *
  rw [← hduhamel]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

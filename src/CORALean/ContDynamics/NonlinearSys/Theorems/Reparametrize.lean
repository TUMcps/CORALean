module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

@[expose] public section

/-!
# Time reparametrization of a classical run

The lemma under Kochdumper and Althoff's pancake time scaling (CORA's
`guardIntersect_pancake`): a classical run of `ẋ = f(x, u)` on `[0, T]` along which a
continuous `g` stays positive is, under the clock `τ(t) = ∫₀ᵗ g(x(r))⁻¹ dr`, a run of
`y' = g(y) f(y, u ∘ σ)` on `[0, τ(T)]`, with `σ = τ⁻¹`. Both runs visit the same states.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Filter intervalIntegral

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The clock `σ` inverse to `τ(t) = ∫₀ᵗ g(x r)⁻¹` carries `[0, τ T]` onto `[0, T]`, has slope
`g(x(σ s))`, and `x ∘ σ` solves the `g`-scaled ODE there with the same set of states. -/
theorem NonlinearSys.reparametrize (sys : NonlinearSys n m) (T : ℝ) (hT : 0 ≤ T)
    (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) (g : Vec ℝ n → ℝ)
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (sys.f (x t) (u t)) (Icc 0 T) t)
    (hgc : ContinuousOn g (x '' Icc 0 T)) (hgp : ∀ t ∈ Icc 0 T, 0 < g (x t)) : -- --- STMT ---
    ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ σ (∫ r in (0 : ℝ)..T, (g (x r))⁻¹) = T ∧
      MapsTo σ (Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹)) (Icc 0 T) ∧
      (∀ s ∈ Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹),
        HasDerivWithinAt σ (g (x (σ s))) (Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹)) s) ∧
      (∀ s ∈ Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹),
        HasDerivWithinAt (x ∘ σ) (g ((x ∘ σ) s) • sys.f ((x ∘ σ) s) (u (σ s)))
          (Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹)) s) ∧
      (x ∘ σ) '' Icc 0 (∫ r in (0 : ℝ)..T, (g (x r))⁻¹) = x '' Icc 0 T := by -- --- PROOF ---
  -- the clamp to `[0, T]` and the integrand extended by constants
  set cl : ℝ → ℝ := fun t => max 0 (min T t) with hcl
  have hclc : Continuous cl := by fun_prop
  have hclI : ∀ t, cl t ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hclid : ∀ t ∈ Icc (0 : ℝ) T, cl t = t := fun t ht => by
    simp [hcl, min_eq_right ht.2, max_eq_right ht.1]
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht => (hx t ht).continuousWithinAt
  -- the integrand, continuous and positive on all of ℝ
  set w : ℝ → ℝ := fun t => (g (x (cl t)))⁻¹ with hw
  have hwpos : ∀ t, 0 < w t := fun t => inv_pos.2 (hgp _ (hclI t))
  have hwc : Continuous w := by
    have h1 : Continuous (x ∘ cl) := hxc.comp_continuous hclc hclI
    have h2 : Continuous (g ∘ (x ∘ cl)) :=
      hgc.comp_continuous h1 (fun t => ⟨cl t, hclI t, rfl⟩)
    exact (h2.inv₀ (fun t => (hgp _ (hclI t)).ne'))
  -- a uniform positive lower bound
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ w t := by
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hwc.continuousOn
    refine ⟨w t₀, hwpos t₀, fun t => ?_⟩
    have := hmin (hclI t)
    have e : w (cl t) = w t := by simp [hw, hclid _ (hclI t)]
    simpa [e] using this
  -- the clock `τ`, a strictly increasing `C¹` map
  set τ : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, w r with hτ
  have hτd : ∀ t, HasDerivAt τ (w t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hwc.intervalIntegrable _ _)
      (hwc.stronglyMeasurableAtFilter _ _) hwc.continuousAt
  have hτmono : StrictMono τ := strictMono_of_deriv_pos (fun t => by
    rw [(hτd t).deriv]; exact hwpos t)
  have hτ0 : τ 0 = 0 := by simp [hτ]
  -- linear growth of `τ` both ways makes it onto
  have hbd₁ : ∀ t, 0 ≤ t → c * t ≤ τ t := fun t h => by
    have := intervalIntegral.integral_mono_on h
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := c))
      (hwc.intervalIntegrable _ _) (fun r _ => hc r)
    simpa [hτ, mul_comm] using this
  have hbd₂ : ∀ t, t ≤ 0 → τ t ≤ c * t := fun t h => by
    have := intervalIntegral.integral_mono_on h
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := c))
      (hwc.intervalIntegrable _ _) (fun r _ => hc r)
    have e : τ t = -∫ r in t..0, w r := by
      simp [hτ, intervalIntegral.integral_symm t 0]
    simp at this; linarith
  -- onto, by the intermediate value theorem
  have hsurj : Function.Surjective τ := by
    apply (continuous_iff_continuousAt.2 fun t => (hτd t).continuousAt).surjective
    · refine tendsto_atTop_mono' _ ?_ (tendsto_id.const_mul_atTop hc0)
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact hbd₁ t ht
    · refine tendsto_atBot_mono' _ ?_ (tendsto_id.const_mul_atBot hc0)
      filter_upwards [eventually_le_atBot 0] with t ht
      exact hbd₂ t ht
  -- the inverse `σ` and its slope
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective τ hτmono hsurj
  set σ : ℝ → ℝ := fun s => e.symm s with hσ
  have hστ : ∀ s, τ (σ s) = s := fun s => e.apply_symm_apply s
  have hσd : ∀ s, HasDerivAt σ (g (x (cl (σ s)))) s := fun s => by
    have h := HasDerivAt.of_local_left_inverse (g := σ) (a := s) e.symm.continuous.continuousAt
      (hτd _) (hwpos _).ne' (Eventually.of_forall hστ)
    simpa [hw] using h
  -- the upper end `τ T` is the integral of the statement
  have hS : (∫ r in (0 : ℝ)..T, (g (x r))⁻¹) = τ T := by
    simp only [hτ]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hT] at hr
    simp [hw, hclid r hr]
  rw [hS]
  -- `σ` fixes the ends and maps `[0, τ T]` into `[0, T]`
  have hσ0 : σ 0 = 0 := by
    have h : σ (τ 0) = 0 := e.symm_apply_apply 0
    rwa [hτ0] at h
  have hσT : σ (τ T) = T := e.symm_apply_apply T
  have hmaps : MapsTo σ (Icc 0 (τ T)) (Icc 0 T) := fun s hs => by
    constructor
    · by_contra h
      have := hτmono (not_le.1 h); rw [hστ, hτ0] at this; linarith [hs.1]
    · by_contra h
      have := hτmono (not_le.1 h); rw [hστ] at this; linarith [hs.2]
  -- the slope of `σ`, then the chain rule for `x ∘ σ`, then the states
  refine ⟨σ, hσ0, hσT, hmaps, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · have := (hσd s).hasDerivWithinAt (s := Icc 0 (τ T))
    rwa [hclid _ (hmaps hs)] at this
  · have h1 : HasDerivWithinAt σ (g (x (σ s))) (Icc 0 (τ T)) s := by
      have := (hσd s).hasDerivWithinAt (s := Icc 0 (τ T))
      rwa [hclid _ (hmaps hs)] at this
    have h2 := (hx _ (hmaps hs)).scomp s h1 hmaps
    simpa using h2
  · ext z
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨σ s, hmaps hs, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨τ t, ⟨?_, ?_⟩, ?_⟩
      · rw [← hτ0]; exact hτmono.monotone ht.1
      · exact hτmono.monotone ht.2
      · show x (σ (τ t)) = x t
        rw [show σ (τ t) = t from e.symm_apply_apply t]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

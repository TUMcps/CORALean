import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A polynomially weighted average stays in a convex closed set

`∫₀ʳ τⁱ f(τ) dτ ∈ (r^{i+1}/(i+1)) · S` whenever `f` is valued in `S` and `S` is
convex and closed — the total weight `∫₀ʳ τⁱ dτ` scaling the set, and nothing
worse. Every term of the input solution of [1, Thm. 3.1] is one instance of it.

An integral is a limit of convex combinations of values of `f`, so convexity is
what puts it in `S` and closedness is what turns the limit into membership.
Boundedness only makes `f` integrable.

Proved by putting the weight into the measure rather than the integrand, so
`Convex.set_average_mem` applies to `f` itself: `⨍` against `τⁱ dτ` is the
normalised integral wanted, normalised by the total weight.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory Pointwise

open scoped ENNReal NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The weighted average of a set-valued function, scaled by the total weight. -/
theorem integral_pow_smul_mem {S : Set (Vec ℝ n)} (hconv : Convex ℝ S) (hclosed : IsClosed S)
    (hbdd : Bornology.IsBounded S) {f : ℝ → Vec ℝ n} {r : ℝ} (hr : 0 < r) (i : ℕ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 r)))
    (hmem : ∀ τ ∈ Set.Ioc (0:ℝ) r, f τ ∈ S) :
    (∫ τ in (0:ℝ)..r, τ ^ i • f τ) ∈ (r ^ (i + 1) / ((i : ℝ) + 1)) • S := by -- --- PROOF ---
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  set t : Set ℝ := Set.Ioc 0 r with ht
  set w : ℝ → NNReal := fun τ => (τ ^ i).toNNReal with hw
  set ν : Measure ℝ := volume.withDensity fun τ => (w τ : ℝ≥0∞) with hν
  -- the weight is what it looks like on `t`, and continuous everywhere
  have hwval : ∀ τ ∈ t, ((w τ : ℝ)) = τ ^ i := by
    intro τ hτ
    exact Real.coe_toNNReal _ (pow_nonneg hτ.1.le i)
  have hwcont : Continuous fun τ : ℝ => ((w τ : ℝ)) := by
    simp only [hw, Real.coe_toNNReal']
    exact (continuous_pow i).max continuous_const
  have hwmeas : Measurable w := (continuous_pow i).measurable.real_toNNReal
  have hwint : IntegrableOn (fun τ : ℝ => ((w τ : ℝ))) t :=
    (hwcont.integrableOn_Icc (a := 0) (b := r)).mono_set Set.Ioc_subset_Icc_self
  -- the total weight
  have htotal : ∫ τ in t, ((w τ : ℝ)) = r ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [ht, ← intervalIntegral.integral_of_le hr.le,
      intervalIntegral.integral_congr (g := fun τ : ℝ => τ ^ i) ?_, integral_pow]
    · simp [zero_pow (Nat.succ_ne_zero i)]
    · intro τ hτ
      rw [Set.uIcc_of_le hr.le] at hτ
      exact Real.coe_toNNReal _ (pow_nonneg hτ.1 i)
  have hW0 : (0:ℝ) < r ^ (i + 1) / ((i : ℝ) + 1) := by positivity
  have hνt : ν t = ENNReal.ofReal (r ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [hν, withDensity_apply _ measurableSet_Ioc, lintegral_coe_eq_integral _ hwint, htotal]
  have hνreal : ν.real t = r ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [measureReal_def, hνt, ENNReal.toReal_ofReal hW0.le]
  -- the restricted measure, with the weight moved back onto the integrand
  have hres : ν.restrict t = (volume.restrict t).withDensity fun τ => (w τ : ℝ≥0∞) :=
    restrict_withDensity measurableSet_Ioc _
  have hac : ν.restrict t ≪ volume.restrict t := by
    rw [hres]
    exact withDensity_absolutelyContinuous _ _
  have hfint : IntegrableOn f t := by
    refine ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := C) measure_Ioc_lt_top ?_⟩
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun τ hτ => hC _ (hmem τ hτ))
  have hmemae : ∀ᵐ τ ∂(volume.restrict t), f τ ∈ S :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun τ hτ => hmem τ hτ)
  have hfintν : IntegrableOn f t ν := by
    haveI : IsFiniteMeasure (ν.restrict t) := ⟨by rw [Measure.restrict_apply_univ, hνt]; simp⟩
    refine ⟨hmeas.mono_ac hac, HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun τ hτ => hC _ (hmem τ hτ))).filter_mono hac.ae_le
  -- the weighted integral, as an average against `ν`
  have hswap : ∫ τ in t, f τ ∂ν = ∫ τ in t, τ ^ i • f τ := by
    rw [hres, integral_withDensity_eq_integral_smul₀ (f := w) hwmeas.aemeasurable]
    refine setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [NNReal.smul_def, hwval τ hτ]
  have h0 : ν t ≠ 0 := by rw [hνt]; simpa using hW0
  have hfin : ν t ≠ ⊤ := by rw [hνt]; exact ENNReal.ofReal_ne_top
  have havg := Convex.set_average_mem hconv hclosed h0 hfin
    (hmemae.filter_mono hac.ae_le) hfintν
  rw [setAverage_eq, hνreal, hswap] at havg
  rw [intervalIntegral.integral_of_le hr.le]
  have := Set.smul_mem_smul_set (a := r ^ (i + 1) / ((i : ℝ) + 1)) havg
  rwa [smul_inv_smul₀ hW0.ne'] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

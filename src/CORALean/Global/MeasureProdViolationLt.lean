import CORALean.Global.BinomialTailStrictAntiOn
import CORALean.Global.PiCountLeMeasureLe
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A bad solution rarely survives `m` independent samples

The integration step of [1, Thm. 3] and [1, Thm. 4] (Appendix B, Eq. B.3): a solution `θ(a)`
read off data `a` of any law `μ_A`, beside `m > k` samples of law `P` independent of it (the
product `μ_A ⊗ Pᵐ`), is bad (violation probability `ζ > ε`) and violated by at most `k` of the
samples with probability below `Σ_{i=0}^k C(m, i) εⁱ(1 - ε)^{m-i}`. Given `a` the samples violate
at most `k` times with probability the tail at `ζ(a)` (`measure_pi_card_filter_le`), below the
tail at `ε` where `ζ(a) > ε` (`binomialTail_strictAntiOn`); integrating over `a` keeps the
inequality strict, also where the bad set is null, as the tail at `ε` is positive.
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
theorem measure_prod_violation_lt {A ι E Δ : Type} [MeasurableSpace A] [Fintype ι]
    [MeasurableSpace E] [MeasurableSpace Δ] (μA : Measure A) [IsProbabilityMeasure μA]
    (P : Measure Δ) [IsProbabilityMeasure P] {C : Set (E × Δ)} (hC : MeasurableSet C)
    {θ : A → E} (hθ : Measurable θ) {k : ℕ} (hk : k < Fintype.card ι) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    (μA.prod (Measure.pi fun _ : ι => P))
        {q | ε < P.real (Prod.mk (θ q.1) ⁻¹' Cᶜ) ∧
          (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k} <
      ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), ((Fintype.card ι).choose i : ℝ) * ε ^ i *
        (1 - ε) ^ (Fintype.card ι - i)) := by -- --- PROOF ---
  set μP := Measure.pi fun _ : ι => P
  set g : ℝ → ℝ := fun p => ∑ i ∈ Finset.range (k + 1),
    ((Fintype.card ι).choose i : ℝ) * p ^ i * (1 - p) ^ (Fintype.card ι - i) with hg
  have hanti : StrictAntiOn g (Set.Icc 0 1) := binomialTail_strictAntiOn hk
  have hgpos : 0 < g ε := by
    simp only [hg]
    rw [Finset.sum_range_succ']
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => by
      have : 0 ≤ 1 - ε := by linarith
      positivity) ?_
    simpa using pow_pos (by linarith : (0 : ℝ) < 1 - ε) _
  let ζ : A → ℝ := fun a => P.real (Prod.mk (θ a) ⁻¹' Cᶜ)
  have hζ : Measurable ζ := ((measurable_measure_prodMk_left hC.compl).comp hθ).ennreal_toReal
  set S := {a | ε < ζ a}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hζ
  set T := {q : A × (ι → Δ) | ε < P.real (Prod.mk (θ q.1) ⁻¹' Cᶜ) ∧
    (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k}
  -- `T` is measurable: the pattern of violations is a measurable finite-valued map
  have hT : MeasurableSet T := by
    let v : A × (ι → Δ) → (ι → Bool) :=
      fun q j => if q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ then true else false
    have hv : Measurable v := measurable_pi_lambda _ fun j => measurable_to_bool (by
      have : (fun q : A × (ι → Δ) =>
          if q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ then true else false) ⁻¹' {true} =
          (fun q : A × (ι → Δ) => (θ q.1, q.2 j)) ⁻¹' Cᶜ := by
        ext q; simp
      rw [this]
      exact hC.compl.preimage ((hθ.comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)))
    have hset : {q : A × (ι → Δ) |
        (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k} =
        v ⁻¹' {w | (Finset.univ.filter fun j => w j = true).card ≤ k} := by
      ext q; simp [v]
    have h2 : MeasurableSet {q : A × (ι → Δ) |
        (Finset.univ.filter fun j => q.2 j ∈ Prod.mk (θ q.1) ⁻¹' Cᶜ).card ≤ k} := by
      rw [hset]; exact (Set.toFinite _).measurableSet.preimage hv
    exact (measurableSet_lt measurable_const (hζ.comp measurable_fst)).inter h2
  -- given `a`, the samples violate at most `k` times with the binomial tail's probability
  have hsec : ∀ a, μP (Prod.mk a ⁻¹' T) ≤ S.indicator (fun a => ENNReal.ofReal (g (ζ a))) a := by
    intro a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]
      have hset : Prod.mk a ⁻¹' T =
          {b | (Finset.univ.filter fun j => b j ∈ Prod.mk (θ a) ⁻¹' Cᶜ).card ≤ k} := by
        ext b
        simp only [T, Set.mem_preimage, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
      rw [hset]
      exact measure_pi_card_filter_le (ι := ι) P
        (measurable_prodMk_left hC.compl : MeasurableSet (Prod.mk (θ a) ⁻¹' Cᶜ)) k
    · have hset : Prod.mk a ⁻¹' T = ∅ := by
        ext b
        simp only [T, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => ha h.1
      simp [hset]
  -- where the solution is bad, the tail is below its value at `ε`
  have hlt : ∀ a ∈ S, g (ζ a) < g ε := fun a ha =>
    hanti ⟨hε.le, hε1.le⟩ ⟨(hε.trans ha).le, measureReal_le_one⟩ ha
  have hfin : ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μA ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const fun a ha =>
      ENNReal.ofReal_le_ofReal (hlt a ha).le)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  -- Fubini, then strict on a bad set of positive measure
  calc (μA.prod μP) T = ∫⁻ a, μP (Prod.mk a ⁻¹' T) ∂μA := Measure.prod_apply hT
    _ ≤ ∫⁻ a, S.indicator (fun a => ENNReal.ofReal (g (ζ a))) a ∂μA := lintegral_mono hsec
    _ = ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μA := lintegral_indicator hS _
    _ < ENNReal.ofReal (g ε) := by
      by_cases hS0 : μA S = 0
      · rw [Measure.restrict_eq_zero.mpr hS0, lintegral_zero_measure]
        exact ENNReal.ofReal_pos.mpr hgpos
      calc ∫⁻ a in S, ENNReal.ofReal (g (ζ a)) ∂μA < ∫⁻ a in S, ENNReal.ofReal (g ε) ∂μA :=
            setLIntegral_strict_mono hS hS0 measurable_const hfin (ae_of_all _ fun a ha =>
              (ENNReal.ofReal_lt_ofReal_iff hgpos).mpr (hlt a ha))
        _ = ENNReal.ofReal (g ε) * μA S := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (g ε) * 1 := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (g ε) := mul_one _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

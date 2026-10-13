import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability survives reflection about the step's endpoint

The reflected form `inputSolution_outer` states its hypothesis in, from the
plain one `inputReach` carries. Reflection is negation followed by a
translation, and both preserve Lebesgue measure; the negation-invariance
instance itself sits behind Haar uniqueness, an import far heavier than the
one fact needed here, so it is taken instead from the scaling law at `-1`.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lebesgue measure is invariant under negation. Taken from the scaling law at
`-1`: the negation-invariance instance itself sits behind Haar uniqueness, an
import far heavier than the one fact needed here. -/
theorem aux_measurePreserving_neg : MeasurePreserving (fun x : ℝ => -x) volume volume := by
  refine ⟨measurable_neg, ?_⟩
  have h := Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
  simpa using h

/-- Reflection is negation followed by a translation, and both preserve the
measure. -/
theorem aux_measurePreserving_sub_left (c : ℝ) :
    MeasurePreserving (fun σ : ℝ => c - σ) volume volume := by
  have h := (measurePreserving_add_left volume c).comp aux_measurePreserving_neg
  simpa [Function.comp_def, sub_eq_add_neg] using h

/-- Reflecting about `c` carries `Icc a b` onto `Icc (c-b) (c-a)` and preserves
Lebesgue measure. -/
theorem aux_aestronglyMeasurable_comp_sub_left {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun σ => f (c - σ))
      (volume.restrict (Set.Icc (c - b) (c - a))) := by -- --- PROOF ---
  have hpre : (fun σ : ℝ => c - σ) ⁻¹' Set.Icc a b = Set.Icc (c - b) (c - a) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => c - σ)
      (volume.restrict (Set.Icc (c - b) (c - a))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (aux_measurePreserving_sub_left c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reflected form `inputSolution_outer` states its hypothesis in, from the
plain one `inputReach` carries. -/
theorem aestronglyMeasurable_reflect_Ioc {u : ℝ → Vec ℝ n} {τ : ℝ}
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 τ))) :
    AEStronglyMeasurable (fun σ => u (τ - σ)) (volume.restrict (Set.Ioc 0 τ)) := by
  have h := aux_aestronglyMeasurable_comp_sub_left (c := τ) hmeas
  rw [sub_zero, sub_self] at h
  exact h.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

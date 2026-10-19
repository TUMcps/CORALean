module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionConstOfZero
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionEqOrbit

@[expose] public section

/-!
# The scaled solution does not pass a zero of the scaling function

If the orbit `z` of `ẋ = f(x)` meets `{g = 0}` at time `M`, the clock `∫₀ᵗ g(y)` of a scaled
solution from `z(0)` stays at most `M`: were it to pass `M`, it would equal `M` at some earlier
time, where `y = z(M)` is a zero of `g · f` and so stays put (`lipschitzSolution_const_of_zero`),
and the clock would not grow after. With `g` the distance to the guard, [1, Sec. 3.3], this is
that the scaled run never crosses `G`, the step [1, Cor. 1] needs.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The clock of a scaled solution from `z 0` stays at most `M` if `g (z M) = 0`. -/
theorem scaledSolution_clock_le {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {g : X → ℝ}
    (hg : Continuous g) {K' : ℝ≥0} (hF : LipschitzWith K' fun x => g x • f x) {y z : ℝ → X}
    {t M : ℝ} (ht : 0 ≤ t) (hy : ∀ u ∈ Icc 0 t, HasDerivAt y (g (y u) • f (y u)) u)
    (hy0 : ∀ u ∈ Icc 0 t, 0 ≤ g (y u)) (hz : ∀ u ∈ Icc 0 M, HasDerivAt z (f (z u)) u)
    (hz0 : z 0 = y 0) (hM : 0 ≤ M) (hgM : g (z M) = 0) : -- --- CONCL ---
    ∫ v in (0 : ℝ)..t, g (y v) ≤ M := by -- --- PROOF ---
  by_contra hlt
  rw [not_le] at hlt
  have hyc : ContinuousOn y (Icc 0 t) := fun u hu => (hy u hu).continuousAt.continuousWithinAt
  -- the clock is continuous, so it equals `M` at some `τ₁ ≤ t`
  have hgy : ContinuousOn (fun v => g (y v)) (Icc 0 t) := hg.comp_continuousOn hyc
  have hσc : ContinuousOn (fun τ => ∫ v in (0 : ℝ)..τ, g (y v)) (Icc 0 t) := by
    have hint : IntervalIntegrable (fun v => g (y v)) MeasureTheory.volume 0 t :=
      (hgy.mono (by simp)).intervalIntegrable_of_Icc ht
    simpa [uIcc_of_le ht] using
      intervalIntegral.continuousOn_primitive_interval' hint (a := 0) (by simp [ht])
  obtain ⟨τ₁, hτ₁, hστ₁⟩ := intermediate_value_Icc ht hσc
    (show M ∈ Icc (∫ v in (0 : ℝ)..0, g (y v)) (∫ v in (0 : ℝ)..t, g (y v)) by
      simpa using ⟨hM, hlt.le⟩)
  simp only at hστ₁
  -- there `y = z M` is a zero of `g`, so it stays, and the clock does not grow after
  have hyτ : y τ₁ = z M := by
    have := scaledSolution_eq_orbit hf hg hτ₁.1 (fun u hu => hy0 u ⟨hu.1, hu.2.trans hτ₁.2⟩)
      (hyc.mono (Icc_subset_Icc le_rfl hτ₁.2))
      (fun u hu => (hy u ⟨hu.1, hu.2.le.trans hτ₁.2⟩).hasDerivWithinAt) hz hz0
      (by rw [hστ₁])
    rwa [hστ₁] at this
  have hconst := lipschitzSolution_const_of_zero hF (a := τ₁) (t := t)
    (fun u hu => hy u ⟨hτ₁.1.trans hu.1, hu.2⟩) (by simp [hyτ, hgM])
  have hzero : ∫ v in τ₁..t, g (y v) = 0 := by
    have : ∀ v ∈ Set.uIcc τ₁ t, g (y v) = 0 := fun v hv => by
      rw [uIcc_of_le hτ₁.2] at hv
      rw [hconst v hv, hyτ, hgM]
    rw [intervalIntegral.integral_congr this]; simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (a := 0) (b := τ₁) (c := t) (f := fun v => g (y v)) (μ := MeasureTheory.volume)
    ((hgy.mono (Icc_subset_Icc le_rfl hτ₁.2)).intervalIntegrable_of_Icc hτ₁.1)
    ((hgy.mono (Icc_subset_Icc hτ₁.1 le_rfl)).intervalIntegrable_of_Icc hτ₁.2)
  rw [hστ₁, hzero, add_zero] at hsum
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

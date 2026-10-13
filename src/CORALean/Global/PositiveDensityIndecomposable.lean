import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# A chain with a positive transition density is indecomposable

`[1, Lemma 2]`, under `[1, Assumption]` (a) and (b): if the one-step law of a chain on `S` has a
density `f(y | x) > 0` with respect to `μ`, there are no two disjoint non-empty closed sets, a set
`A` being closed when it cannot be left, `P(Aᶜ | x) = 0` for `x ∈ A`. Smith argues with a third
set `Ā = S \ (A₁ ∪ A₂)` and the positive measure of one of the three; here a closed set's
complement is `μ`-null outright, which gives the same contradiction. `μ` is the reference measure,
nonzero (`λ(S) = 1` in the paper).

## References

* [1] R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed
      Over Bounded Regions". Operations Research 32(6), pp. 1296-1308, 1984.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ENNReal

variable {S : Type} [MeasurableSpace S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem positiveDensity_indecomposable (μ : Measure S) (hμ : μ ≠ 0) (f : S → S → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (hpos : ∀ x y, 0 < f x y)
    (A₁ A₂ : Set S) (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂)
    (hne₁ : A₁.Nonempty) (hne₂ : A₂.Nonempty) (hdisj : Disjoint A₁ A₂)
    (hcl₁ : ∀ x ∈ A₁, ∫⁻ y in A₁ᶜ, f x y ∂μ = 0)
    (hcl₂ : ∀ x ∈ A₂, ∫⁻ y in A₂ᶜ, f x y ∂μ = 0) : False := by -- --- PROOF ---
  -- a closed set has a null complement: the density is positive
  have hnull : ∀ A : Set S, MeasurableSet A → ∀ x, ∫⁻ y in Aᶜ, f x y ∂μ = 0 → μ Aᶜ = 0 := by
    intro A hA x hx
    have hxm : Measurable (f x) := hf.comp measurable_prodMk_left
    rw [setLIntegral_eq_zero_iff hA.compl hxm] at hx
    refine (measure_eq_zero_iff_ae_notMem).mpr (hx.mono fun y hy hyA => ?_)
    exact (hpos x y).ne' (hy hyA)
  obtain ⟨x₁, hx₁⟩ := hne₁
  obtain ⟨x₂, hx₂⟩ := hne₂
  have hn₂ : μ A₂ᶜ = 0 := hnull A₂ h₂ x₂ (hcl₂ x₂ hx₂)
  have hn₁ : μ A₁ᶜ = 0 := hnull A₁ h₁ x₁ (hcl₁ x₁ hx₁)
  -- `A₁ ⊆ A₂ᶜ`, so both `A₁` and its complement are null, and so is the whole space
  have hA₁ : μ A₁ = 0 := measure_mono_null hdisj.subset_compl_right hn₂
  have hU : μ Set.univ = 0 := by
    rw [← Set.union_compl_self A₁]
    exact measure_union_null hA₁ hn₁
  exact hμ (Measure.measure_univ_eq_zero.mp hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

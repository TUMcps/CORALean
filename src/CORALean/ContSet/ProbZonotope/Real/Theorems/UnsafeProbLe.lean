module

public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# The probability of an unsafe set, bounded by heights times volumes

[1, Eq. 7] corrected: if the density `f` of the state is at most `hᵢ` on each region `Qᵢ`,
and the regions cover the confidence set `E`, then
`P(X ∈ B) ≤ P(X ∉ E) + Σᵢ hᵢ V(Qᵢ ∩ B)`. [1] builds exactly these heights `h₁^max, h₂^max, …`
of the enclosing probabilistic hull on the confidence rings `Qᵢ` (Fig. 5) and then prints
`p̄ = 1 - erf(γ/√2)^{2n} + Σᵢ V(Qᵢ ∩ B)`, dropping them: a volume is not a probability
(`UnsafeProbPrinted`). [1]'s `1 - erf(γ/√2)^{2n}` is its bound on `P(X ∉ E)`,
here whatever `(μ.withDensity f) Eᶜ` is.

## Inputs
* `μ` – measure
* `f` – `α → ℝ≥0∞`
* `E` – set of points
* `B` – set of points
* `k` – natural number
* `Q` – sets indexed by `Fin k`
* `h` – family indexed by `Fin k`

## Hypotheses
* `hB` – `MeasurableSet B`
* `hQ` – every `Q i` is measurable
* `hE` – `E ⊆ ⋃ i, Q i`
* `hf` – `f` is at most `h i` on each `Q i`

## Conclusion
* the probability of an unsafe set, bounded by heights times volumes

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory
open scoped ENNReal

variable {α : Type} [MeasurableSpace α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem unsafe_prob_le (μ : Measure α) (f : α → ℝ≥0∞) {E B : Set α} {k : ℕ}
    (Q : Fin k → Set α) (h : Fin k → ℝ≥0∞) (hB : MeasurableSet B)
    (hQ : ∀ i, MeasurableSet (Q i)) (hE : E ⊆ ⋃ i, Q i)
    (hf : ∀ i, ∀ x ∈ Q i, f x ≤ h i) : -- --- CONCL ---
    μ.withDensity f B ≤ μ.withDensity f Eᶜ + ∑ i, h i * μ (Q i ∩ B) := by -- --- PROOF ---
  -- `B` lies outside `E` or in some `Qᵢ ∩ B`
  have hsub : B ⊆ Eᶜ ∪ ⋃ i, (Q i ∩ B) := by
    intro x hx
    by_cases hxE : x ∈ E
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hE hxE)
      exact Or.inr (Set.mem_iUnion.2 ⟨i, hi, hx⟩)
    · exact Or.inl hxE
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  -- on `Qᵢ` the density is at most `hᵢ`
  rw [withDensity_apply _ ((hQ i).inter hB), ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun x hx => hf i x hx.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

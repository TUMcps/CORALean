module

public import Mathlib.Probability.Kernel.Invariance

@[expose] public section

/-!
# A Markov kernel with a symmetric density leaves the reference measure invariant

`[1, Lemma 1]`, under `[1, Assumption]` (a): if the one-step law of a chain on `S` has a density
`f(y | x)` with respect to the measure `μ` and the density is symmetric, `f(y | x) = f(x | y)`,
then `μ` is a stationary initial distribution (`∫ P(A | x) μ(dx) = μ(A)`). For the uniform
distribution on `S` take `μ` the restriction of Lebesgue measure to `S`: stationarity is
homogeneous in `μ`, so `λ = V / V(S)` is stationary as well. The proof is Fubini on `f ≥ 0`, as
printed; here it goes through Mathlib's `Kernel.IsReversible`, whose detailed balance is that
interchange.

## Inputs
* `μ` – reference measure
* `κ` – Markov kernel of the chain
* `f` – transition density

## Hypotheses
* `hf` – the density is measurable
* `hκ` – the kernel has this density with respect to the measure
* `hsymm` – the density is symmetric

## Conclusion
* the reference measure is invariant for the kernel

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

open MeasureTheory ProbabilityTheory ENNReal

variable {S : Type} [MeasurableSpace S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem symmetricDensity_invariant (μ : Measure S) [SFinite μ] (κ : Kernel S S)
    [IsMarkovKernel κ] (f : S → S → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hκ : ∀ x A, MeasurableSet A → κ x A = ∫⁻ y in A, f x y ∂μ)
    (hsymm : ∀ x y, f x y = f y x) : κ.Invariant μ := by -- --- PROOF ---
  -- invariance is detailed balance, by Mathlib
  refine Kernel.IsReversible.invariant fun A B hA hB => ?_
  -- unfold both flows through the density
  have h1 : ∫⁻ x in A, κ x B ∂μ = ∫⁻ x in A, ∫⁻ y in B, f x y ∂μ ∂μ :=
    setLIntegral_congr_fun hA fun x _ => hκ x B hB
  have h2 : ∫⁻ x in B, κ x A ∂μ = ∫⁻ x in B, ∫⁻ y in A, f x y ∂μ ∂μ :=
    setLIntegral_congr_fun hB fun x _ => hκ x A hA
  -- Fubini (Tonelli) swaps the two integrals, the symmetry of `f` closes the gap
  rw [h1, h2, lintegral_lintegral_swap (hf.aemeasurable)]
  exact lintegral_congr fun y => lintegral_congr fun x => hsymm x y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

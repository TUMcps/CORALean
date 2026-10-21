module

public import Mathlib.Topology.Order.IntermediateValue
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionConstOfZero

@[expose] public section

/-!
# A scaled solution keeps the sign of its scaling function

[1, Sec. 3.3] takes `g(x) = (b - a·x) / ‖a‖`, "nonnegative for any `x` in `m₁`". The scaled
solution starts in `m₁`, and stays where `g ≥ 0`: were `g(y)` negative somewhere it would be
zero earlier, by the intermediate value theorem, and `y` would stay at a zero of `g · f` from then
on (`lipschitzSolution_const_of_zero`), a contradiction. [1, Cor. 1] needs it for
`g(x) = (b - a·x) / ‖a‖`.

## Inputs
* `f` – vector field
* `g` – scaling function
* `K'` – Lipschitz constant of the scaled field
* `y` – scaled solution
* `t` – duration

## Hypotheses
* `hg` – scaling function continuous
* `hF` – scaled field is Lipschitz
* `hy` – curve solves the scaled field
* `h0` – scaling function nonnegative at the start

## Conclusion
* scaling function stays nonnegative along the curve

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modelling and Analysis of Timed
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

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of `ẏ = g(y) f(y)` that starts with `g ≥ 0` keeps `g(y) ≥ 0`. -/
theorem scaledSolution_nonneg {f : X → X} {g : X → ℝ} (hg : Continuous g) {K' : ℝ≥0}
    (hF : LipschitzWith K' fun x => g x • f x) {y : ℝ → X} {t : ℝ}
    (hy : ∀ u ∈ Icc 0 t, HasDerivAt y (g (y u) • f (y u)) u) (h0 : 0 ≤ g (y 0)) : -- --- CONCL ---
    ∀ u ∈ Icc 0 t, 0 ≤ g (y u) := by -- --- PROOF ---
  intro u₁ hu₁
  by_contra hneg
  rw [not_le] at hneg
  -- a zero of `g ∘ y` on `[0, u₁]`
  have hc : ContinuousOn (fun u => g (y u)) (Icc 0 u₁) := fun u hu =>
    (hg.continuousAt.comp (hy u ⟨hu.1, hu.2.trans hu₁.2⟩).continuousAt).continuousWithinAt
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc' hu₁.1 hc ⟨hneg.le, h0⟩
  -- `y` stays at the zero from `τ` on
  have hconst := lipschitzSolution_const_of_zero hF (a := τ) (t := t)
    (fun u hu => hy u ⟨hτ.1.trans hu.1, hu.2⟩) (by simp [hτ0])
  have := hconst u₁ ⟨hτ.2, hu₁.2⟩
  simp only at hτ0
  rw [this, hτ0] at hneg
  exact lt_irrefl _ hneg

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

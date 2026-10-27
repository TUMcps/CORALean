module

public import CORALean.ContSet.HPolytope.Real.Counterexamples.IneqsSubsetIff
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `[1, Prop. 1]` fails at an empty summand

At `N = 1`, `x̄ = 0`, `X₁ = I` the proposition is `[1, Lemma 1]`, and the same empty inbody
(`ineqs_subset_iff_counterexample`) lies in the unit box with no `Λ₁` assembling the box's
rows. So "only if" needs every `Pᵢ` nonempty (`sum_ahPolytope_subset_ineqs_iff`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Prop. 1]` fails at an empty summand

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.sum_ahPolytope_subset_ineqs_iff_counterexample : -- --- CONCL ---
    ∃ (Hx : Mat ℝ 3 2) (hx : Vec ℝ 3) (Hy : Mat ℝ 4 2) (hy : Vec ℝ 4),
      {x | ∃ p : Fin 1 → Vec ℝ 2, (∀ i, p i ∈ (HPolytope.ineqs Hx hx).construct) ∧
          x = 0 + ∑ i, (1 : Mat ℝ 2 2) *ᵥ p i} ⊆ (HPolytope.ineqs Hy hy).construct ∧
      ¬ ∃ Λ : Fin 1 → Mat ℝ 4 3, (∀ i j k, 0 ≤ Λ i j k) ∧ (∀ i, Λ i * Hx = Hy * (1 : Mat ℝ 2 2)) ∧
        ∑ i, Λ i *ᵥ hx ≤ hy - Hy *ᵥ 0 := by -- --- PROOF ---
  obtain ⟨Hx, hx, Hy, hy, -, -, hsub, hno⟩ := HPolytope.ineqs_subset_iff_counterexample
  refine ⟨Hx, hx, Hy, hy, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa using hsub (hp 0)
  -- a `Λ₁` here would be a `Λ` for `[1, Lemma 1]`
  · rintro ⟨Λ, hΛ, h1, h2⟩
    exact hno ⟨Λ 0, hΛ 0, by simpa [Matrix.mul_one] using h1 0, by simpa using h2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

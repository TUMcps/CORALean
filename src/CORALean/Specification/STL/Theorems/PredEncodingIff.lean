module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.AbsoluteValue.Basic

@[expose] public section

/-!
# The predicate constraints decide the predicate

[1, Sec. IV-B.1]: `μ(xₜ) ≤ Mₜ zₜ - εₜ` and `-μ(xₜ) ≤ Mₜ(1 - zₜ) - εₜ`, `zₜ ∈ {0, 1}`, enforce
`zₜ = 1` iff `μ(xₜ) > 0`, for `εₜ > 0`, and with [1, Sec. IV-B.2]'s negation `1 - zₜ = 1` iff
`¬ μ`. They are satisfiable when `M` is large and `ε` small enough for the value at hand,
`ε ≤ |μ(xₜ)| ≤ M - ε`: a run with `0 < |μ(xₜ)| < ε` is cut off, as "bound `μ(xₜ)` away from `0`"
says.

## Inputs
* `μ` – predicate value
* `M` – big constant
* `ε` – tolerance

## Hypotheses
* `hε` – the tolerance is positive

## Conclusion
* the constraints decide whether the value is positive

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia.
      "Model Predictive Control with Signal Temporal Logic Specifications". 53rd IEEE Conference on
      Decision and Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.pred_encoding_iff {μ M ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    (∀ z : ℝ, (z = 0 ∨ z = 1) → μ ≤ M * z - ε → -μ ≤ M * (1 - z) - ε →
      ((z = 1 ↔ 0 < μ) ∧ (1 - z = 1 ↔ ¬ 0 < μ))) ∧
    (ε ≤ |μ| → |μ| ≤ M - ε →
      ∃ z : ℝ, (z = 0 ∨ z = 1) ∧ μ ≤ M * z - ε ∧ -μ ≤ M * (1 - z) - ε) := by -- --- PROOF ---
  refine ⟨fun z hz h1 h2 => ?_, fun hlo hhi => ?_⟩
  · -- `z = 1` forces `μ ≥ ε`, `z = 0` forces `μ ≤ -ε`
    rcases hz with rfl | rfl
    · exact ⟨⟨fun h => absurd h (by norm_num), fun h => by linarith⟩,
        ⟨fun _ h => by linarith, fun _ => by norm_num⟩⟩
    · exact ⟨⟨fun _ => by linarith, fun _ => rfl⟩,
        ⟨fun h => absurd h (by norm_num), fun h => absurd (by linarith) h⟩⟩
  · -- the sign of `μ` picks `z`
    rcases le_or_gt 0 μ with hμ | hμ
    · rw [abs_of_nonneg hμ] at hlo hhi
      exact ⟨1, Or.inr rfl, by linarith, by linarith⟩
    · rw [abs_of_neg hμ] at hlo hhi
      exact ⟨0, Or.inl rfl, by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

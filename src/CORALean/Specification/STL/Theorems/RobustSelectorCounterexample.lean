import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The selector of the minimum is not unique

[1, Eq. 5] is said to enforce `r = rⱼ` iff `pⱼ = 1`. The "if" holds, with (4): `pⱼ = 1` makes
(5) read `rⱼ ≤ r`. The "only if" fails when two operands tie: `r₁ = r₂ = 0`, `p = (1, 0)`,
`r = 0` and `M = 1` satisfy (3)-(5), and `r = r₂` with `p₂ = 0`. `STL.robust_conj_encoding` does
not need it: `r = minᵢ rᵢ` holds either way.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.robust_selector_counterexample :
    (∀ {m : ℕ} (rs p : Fin m → ℝ) (r M : ℝ) (j : Fin m), (∀ i, r ≤ rs i) →
      (∀ i, rs i - (1 - p i) * M ≤ r ∧ r ≤ rs i + M * (1 - p i)) → p j = 1 → r = rs j) ∧
    let rs : Fin 2 → ℝ := ![0, 0]
    let p : Fin 2 → ℝ := ![1, 0]
    let r : ℝ := 0
    let M : ℝ := 1
    ∑ i, p i = 1 ∧ (∀ i, r ≤ rs i) ∧
      (∀ i, rs i - (1 - p i) * M ≤ r ∧ r ≤ rs i + M * (1 - p i)) ∧
      r = rs 1 ∧ p 1 ≠ 1 := by -- --- PROOF ---
  -- the "if": `pⱼ = 1` makes (5) read `rⱼ ≤ r`, and (4) is the other half
  refine ⟨fun rs p r M j h4 h5 hj => le_antisymm (h4 j) ?_, ?_⟩
  · have := (h5 j).1
    rw [hj] at this
    linarith
  intro rs p r M
  refine ⟨by simp [p, Fin.sum_univ_two], fun i => ?_, fun i => ?_, by simp [r, rs], by simp [p]⟩
  · fin_cases i <;> simp [r, rs]
  · fin_cases i <;> norm_num [r, rs, p, M]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

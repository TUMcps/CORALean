module

public import CORALean.Specification.STL.Definitions.MILPEncoding
public import Mathlib.Tactic.NormNum
public import CORALean.Specification.STL.Operations.DFormulaBound
public import CORALean.Specification.STL.Operations.DFormulaRob

@[expose] public section

/-!
# The printed robust encoding misses the robustness

[1, Sec. V (correctness)] claims the encoding enforces `r^φ_t = ρ^φ(x, t)` and `r^φ_t > 0` iff
`φ` holds at `t`. On the run of `STL.DFormula.zEnc_counterexample`, with the until encoded by
`r_t = max(r^{μ₂}_t, min(r^{μ₁}_t, r_{t+1}))` as printed, `r^φ_0 = 1 > 0` while
`ρ^φ(x, 0) = -1 < 0` and the formula is false: not a boundary case but a sign error.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed robust encoding is positive though the robustness is negative

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

theorem STL.DFormula.rEnc_counterexample : -- --- CONCL ---
    let x : ℕ → ℝ × ℝ := fun t => if t = 0 then (1, -1) else (-1, 1)
    let φ : STL.DFormula (ℝ × ℝ) := .until 0 1 (by norm_num) (.pred Prod.fst) (.pred Prod.snd)
    φ.bound ≤ 1 ∧ 0 < φ.rEnc 1 false x 0 ∧ φ.rob x 0 < 0 := by -- --- PROOF ---
  intro x φ
  -- the encoding through `r₁ = r^{μ₂}_1 = 1`, the robustness `-1` at both witnesses
  refine ⟨by simp [φ, STL.DFormula.bound], ?_, ?_⟩
  · simp only [φ, STL.DFormula.rEnc, lt_min_iff, Finset.lt_inf'_iff, Finset.lt_sup'_iff]
    refine ⟨⟨fun i hi => ?_, ⟨1, by simp, by norm_num [x]⟩⟩, ?_⟩
    · simp at hi; subst hi; norm_num [x]
    · rw [STL.untilRob]
      simp only [Bool.false_eq_true, if_false]
      rw [STL.untilRob]
      norm_num [x]
  · simp only [φ, STL.DFormula.rob, Finset.sup'_lt_iff, min_lt_iff, Finset.inf'_lt_iff]
    rintro ⟨t', ht'⟩ -
    have ht := Finset.mem_Icc.mp ht'
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using ht.2) with h | h
    · left; simp only [h]; norm_num [x]
    · right; exact ⟨1, by simp [h], by norm_num [x]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

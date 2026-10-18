module

public import CORALean.Specification.STL.Definitions.MILPEncoding
public import Mathlib.Tactic.NormNum
public import CORALean.Specification.STL.Operations.DFormulaBound

@[expose] public section

/-!
# The printed Boolean encoding misses the semantics

[1, Sec. IV-B.3 (correctness)] claims `z^φ_t = 1` iff `φ` holds at `t`. Two ways it fails as
printed. The until, [1, Sec. IV-B.3 (until)]: on the run `(1, -1), (-1, 1), …` with
`μ₁ = x⁽¹⁾`, `μ₂ = x⁽²⁾`, `μ₁ U[0,1] μ₂` is false at `0` (`μ₂` first holds at `1`, where `μ₁`
fails, and the printed semantics asks `μ₁` through that step), while the encoding with
`z_t = z^{μ₂}_t ∨ (z^{μ₁}_t ∧ z_{t+1})` says true, the horizon `N = 1` covering the bound. The
horizon, [1, Sec. IV-B.3 (temporal)]: with `N = 0` the window of `□[0,1] μ₁` is truncated to
`[0, 0]`, and the encoding says true where the formula is false.

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

theorem STL.DFormula.zEnc_counterexample : -- --- STMT ---
    let x : ℕ → ℝ × ℝ := fun t => if t = 0 then (1, -1) else (-1, 1)
    let φ : STL.DFormula (ℝ × ℝ) := .until 0 1 (by norm_num) (.pred Prod.fst) (.pred Prod.snd)
    let χ : STL.DFormula (ℝ × ℝ) := .always 0 1 (by norm_num) (.pred Prod.fst)
    φ.bound ≤ 1 ∧ φ.zEnc 1 false x 0 ∧ ¬ φ.Sat x 0 ∧
      χ.zEnc 0 true x 0 ∧ ¬ χ.Sat x 0 := by -- --- PROOF ---
  intro x φ χ
  -- the bound, then the strict until true and the formula false, then the truncation
  refine ⟨by simp [φ, STL.DFormula.bound], ?_, ?_, ?_, ?_⟩
  · simp only [φ, STL.DFormula.zEnc]
    refine ⟨fun i hi => ?_, ⟨1, by simp, by simp [x]⟩, ?_⟩
    · simp at hi; subst hi; simp [x]
    · rw [STL.untilEnc]
      simp only [Bool.false_eq_true, if_false]
      right
      refine ⟨by simp [x], ?_⟩
      rw [STL.untilEnc]
      simp [x]
  -- the formula: `μ₂` fails at `0`, and at `1` `μ₁` fails
  · simp only [φ, STL.DFormula.Sat]
    rintro ⟨t', ht', hψ, hφ⟩
    simp at ht'
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht' with rfl | rfl
    · norm_num [x] at hψ
    · have h1 : (0 : ℝ) < (x 1).1 := hφ 1 (by simp)
      norm_num [x] at h1
  -- the truncated `□[0,1]` reads step `0` alone
  · simp only [χ, STL.DFormula.zEnc]
    intro i hi
    simp at hi; subst hi; simp [x]
  · simp only [χ, STL.DFormula.Sat]
    intro h
    have := h 1 (by simp)
    norm_num [x] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

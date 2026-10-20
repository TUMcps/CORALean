module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A quadratic with negative leading coefficient is eventually negative

`a s² + b s + c < 0` for every `s` from some `s₀` on, when `a < 0`, with the explicit
threshold `s₀ = max 1 ((|b| + |c| + 1) / (-a))`. The S-lemma reads its homogenized forms at
`t = 0` through this: a quadratic in `x` that is non-negative everywhere has a non-negative
leading form.

## Inputs
* `a` – leading coefficient
* `b` – linear coefficient
* `c` – constant coefficient

## Hypotheses
* `ha` – the leading coefficient is negative

## Conclusion
* the quadratic is negative from some threshold on
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `a < 0`, `a s² + b s + c < 0` for all `s ≥ s₀`. -/
theorem exists_quad_neg {a : ℝ} (ha : a < 0) (b c : ℝ) :
    ∃ s₀ : ℝ, ∀ s, s₀ ≤ s → a * s ^ 2 + b * s + c < 0 := by -- --- PROOF ---
  refine ⟨max 1 ((|b| + |c| + 1) / -a), fun s hs => ?_⟩
  have h1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have h2 : (|b| + |c| + 1) / -a ≤ s := le_trans (le_max_right _ _) hs
  rw [div_le_iff₀ (by linarith)] at h2
  -- `b s + c ≤ (|b| + |c|) s ≤ -a s² - s`
  have hb : b * s ≤ |b| * s := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
  have hc : c ≤ |c| * s := (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) h1)
  nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

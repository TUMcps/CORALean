module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aux_log_` is sound

`aux_log_` keeps every solution of `log s ∈ int` with `s > 0`.

## Inputs
* `prev` – previous interval

## Hypotheses
* `hd` – the interval is positive

## Conclusion
* the inverse of the logarithm keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_log_` is sound for `log` on a positive operand. -/
theorem SyntaxTree.log_sound (prev : Dom) (hd : 0 < prev.inf 0) :
    UnarySound Unary.log.fn prev (Real.Interval.log prev) funHanLog := by -- --- PROOF ---
  intro int _ s hs hi
  have hs0 : 0 < s := hd.trans_le hs.1
  have h : int.inf 0 ≤ Real.log s ∧ Real.log s ≤ int.sup 0 := hi
  have l₁ : Real.exp (int.inf 0) ≤ s := by
    rw [← Real.exp_log hs0]; exact Real.exp_le_exp.2 h.1
  have l₂ : s ≤ Real.exp (int.sup 0) := by
    rw [← Real.exp_log hs0]; exact Real.exp_le_exp.2 h.2
  obtain ⟨h₁, h₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
  exact ⟨_, rfl, h₁, h₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

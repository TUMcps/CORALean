module

public import CORALean.ContSet.Interval.Real.Operations.Exp
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.RestrictContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_exp_` is sound

`aux_exp_` keeps every solution of `exp s ∈ int`; `log(0) = -Inf` is the extended bound.

## Inputs
* `a` – nonnegative bound
* `s` – real exponent

## Hypotheses
* `ha` – the bound is nonnegative
* `h` – the bound is at most the exponential

## Conclusion
* the extended logarithm of the bound is at most the exponent
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The extended logarithm of a bound that `exp s` reaches is at most `s`. -/
private theorem SyntaxTree.logE_le {a s : ℝ} (ha : 0 ≤ a) (h : a ≤ Real.exp s) :
    (if a = 0 then ⊥ else ((Real.log a : ℝ) : EReal) : EReal) ≤ s := by
  by_cases h0 : a = 0
  · simp [h0]
  · simp only [h0, if_false, EReal.coe_le_coe_iff]
    exact Real.log_le_iff_le_exp (lt_of_le_of_ne ha (Ne.symm h0)) |>.2 h

/-- The extended logarithm of a bound that `exp s` stays below is at least `s`. -/
private theorem SyntaxTree.le_logE {a s : ℝ} (ha : 0 < a) (h : Real.exp s ≤ a) :
    (s : EReal) ≤ (if a = 0 then ⊥ else ((Real.log a : ℝ) : EReal) : EReal) := by
  simp only [ha.ne', if_false, EReal.coe_le_coe_iff]
  exact Real.le_log_iff_exp_le ha |>.2 h

/-- `aux_exp_` is sound for `exp`. -/
theorem SyntaxTree.exp_sound (prev : Dom) :
    UnarySound Unary.exp.fn prev (Real.Interval.exp prev) funHanExp := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.exp s ∧ Real.exp s ≤ int.sup 0 := hi
  have hpos : 0 < int.sup 0 := (Real.exp_pos s).trans_le h.2
  have hnd : ¬ int.sup 0 < 0 := not_lt.2 hpos.le
  have hsup := le_logE hpos h.2
  unfold funHanExp
  by_cases hl : int.inf 0 < 0
  · simp only [hl, hnd, if_true, if_false, interval]
    have h₁ : (min (⊥ : EReal) (if int.sup 0 = 0 then ⊥ else ((Real.log (int.sup 0) : ℝ) : EReal)))
        ≤ s :=
      (min_le_left _ _).trans bot_le
    obtain ⟨c, w⟩ := restrict_contains hs (lo := min _ _) (hi := max _ _) h₁ (hsup.trans
        (le_max_right _ _))
    exact ⟨_, rfl, c, w⟩
  -- unfold the definitions
  · simp only [hl, hnd, if_false]
    have h₁ := (min_le_left _ (if int.sup 0 = 0 then ⊥ else ((Real.log (int.sup 0) : ℝ) :
        EReal))).trans
      (logE_le (not_lt.1 hl) h.1)
    obtain ⟨c, w⟩ := restrict_contains hs (lo := min _ _) (hi := max _ _) h₁ (hsup.trans
        (le_max_right _ _))
    exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

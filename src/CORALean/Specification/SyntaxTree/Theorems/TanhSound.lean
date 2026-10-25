module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.RestrictContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_tanh_` is sound

`aux_tanh_` keeps every solution of `tanh s ∈ int`; `atanh(±1) = ±Inf` is the extended bound.

## Inputs
* `x` – bound
* `s` – real argument

## Hypotheses
* `h` – the bound is at most the hyperbolic tangent
* `h₁` – the bound is at least minus one

## Conclusion
* the extended inverse of the bound is at most the argument
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The extended `atanh` of a bound below `tanh s` is at most `s`. -/
private theorem SyntaxTree.atanhE_le {x s : ℝ} (h : x ≤ Real.tanh s)
    (h₁ : -1 ≤ x) : -- --- CONCL ---
    (if x = -1 then ⊥ else if x = 1 then ⊤ else ↑(Real.artanh x) : EReal) ≤ s := by -- --- PROOF ---
  by_cases hx : x = -1
  · simp [hx]
  · have hx1 : x ≠ 1 := (h.trans_lt (Real.tanh_lt_one s)).ne
    simp only [hx, hx1, if_false, EReal.coe_le_coe_iff]
    calc Real.artanh x ≤ Real.artanh (Real.tanh s) :=
          Real.artanh_le_artanh (lt_of_le_of_ne h₁ (Ne.symm hx)) (Real.tanh_lt_one s) h
      _ = s := Real.artanh_tanh s

/-- The extended `atanh` of a bound above `tanh s` is at least `s`. -/
private theorem SyntaxTree.le_atanhE {x s : ℝ} (h : Real.tanh s ≤ x) (h₁ : x ≤ 1) : -- --- CONCL ---
    (s : EReal) ≤ (if x = -1 then ⊥ else if x = 1 then ⊤ else ↑(Real.artanh x) :
      EReal) := by -- --- PROOF ---
  have hx : x ≠ -1 := (lt_of_lt_of_le (Real.neg_one_lt_tanh s) h).ne'
  by_cases hx1 : x = 1
  · simp [hx1, show (1 : ℝ) ≠ -1 by norm_num]
  · simp only [hx, hx1, if_false, EReal.coe_le_coe_iff]
    calc s = Real.artanh (Real.tanh s) := (Real.artanh_tanh s).symm
      _ ≤ Real.artanh x := Real.artanh_le_artanh (Real.neg_one_lt_tanh s)
          (lt_of_le_of_ne h₁ hx1) h

/-- `aux_tanh_` is sound for `tanh`. -/
theorem SyntaxTree.tanh_sound (prev : Dom) : -- --- CONCL ---
    IsUnarySound Unary.tanh.fn prev (Real.Interval.tanh prev) funHanTanh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.tanh s ∧ Real.tanh s ≤ int.sup 0 := hi
  have l₁ := atanhE_le (x := max (int.inf 0) (-1)) (s := s)
    (max_le h.1 (Real.neg_one_lt_tanh s).le) (le_max_right _ _)
  have l₂ := le_atanhE (x := min (int.sup 0) 1) (s := s)
    (le_min h.2 (Real.tanh_lt_one s).le) (min_le_right _ _)
  unfold funHanTanh
  simp only [Real.Interval.intersection, interval]
  obtain ⟨c, w⟩ := restrict_contains hs (lo := min _ _) (hi := max _ _)
    ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

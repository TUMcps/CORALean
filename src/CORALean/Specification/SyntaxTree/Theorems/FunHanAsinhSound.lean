module

public import CORALean.ContSet.Interval.Real.Operations.Asinh
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aaux_sinh_` is sound

`aaux_sinh_` keeps every solution of `asinh s ∈ int`.

## Inputs
* `prev` – previous interval

## Hypotheses
* none

## Conclusion
* the inverse of the inverse hyperbolic sine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_sinh_` is sound for `asinh`. -/
theorem SyntaxTree.funHanAsinh_sound (prev : Dom) : -- --- CONCL ---
    IsUnarySound Unary.asinh.fn prev (Real.Interval.asinh prev) funHanAsinh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.arsinh s ∧ Real.arsinh s ≤ int.sup 0 := hi
  have l₁ : Real.sinh (int.inf 0) ≤ s := by
    rw [← Real.sinh_arsinh s]; exact Real.sinh_le_sinh.2 h.1
  have l₂ : s ≤ Real.sinh (int.sup 0) := by
    rw [← Real.sinh_arsinh s]; exact Real.sinh_le_sinh.2 h.2
  obtain ⟨h₁, h₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
  exact ⟨_, rfl, h₁, h₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

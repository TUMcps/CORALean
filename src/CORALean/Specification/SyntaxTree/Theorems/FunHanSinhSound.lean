module

public import CORALean.ContSet.Interval.Real.Operations.Sinh
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aux_sinh_` is sound

`aux_sinh_` (without the cut to `[-1,1]`) keeps every solution of `sinh s ∈ int`.

## Inputs
* `prev` – previous interval

## Hypotheses
* none

## Conclusion
* the inverse of the hyperbolic sine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_sinh_` is sound for `sinh`. -/
theorem SyntaxTree.funHanSinh_sound (prev : Dom) : -- --- CONCL ---
    IsUnarySound Unary.sinh.fn prev (Real.Interval.sinh prev) funHanSinh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.sinh s ∧ Real.sinh s ≤ int.sup 0 := hi
  have l₁ : Real.arsinh (int.inf 0) ≤ s := by
    rw [← Real.arsinh_sinh s]; exact Real.arsinh_le_arsinh.2 h.1
  have l₂ : s ≤ Real.arsinh (int.sup 0) := by
    rw [← Real.arsinh_sinh s]; exact Real.arsinh_le_arsinh.2 h.2
  obtain ⟨h₁, h₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
  exact ⟨_, rfl, h₁, h₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

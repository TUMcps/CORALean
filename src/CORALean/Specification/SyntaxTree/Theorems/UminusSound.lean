module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_uminus_` is sound

`aux_uminus_` keeps every solution of `-x ∈ int`.

## Inputs
* `prev` – previous interval

## Hypotheses
* none

## Conclusion
* the inverse of the negation keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_uminus_` is sound for `uminus`. -/
theorem SyntaxTree.uminus_sound (prev : Dom) : -- --- CONCL ---
    IsUnarySound Unary.uminus.fn prev (Real.Interval.uminus prev)
    funHanUminus := by -- --- PROOF ---
  intro int _ s hs hi
  refine ⟨_, rfl, ?_, ?_⟩ <;>
  simp only [Unary.fn, Dom.contains, Dom.IsWithin, Real.Interval.intersection,
    Real.Interval.uminus, Pi.neg_apply] at hs hi ⊢
  · exact ⟨max_le (by linarith [hi.2]) hs.1, le_min (by linarith [hi.1]) hs.2⟩
  · exact ⟨le_max_right _ _, min_le_right _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

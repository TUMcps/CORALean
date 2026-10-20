module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.BinarySound
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_minus_` is sound

`aux_minus_` keeps every solution of `x₁ - x₂ ∈ int`.

## Inputs
* `prev₁` – first previous interval
* `prev₂` – second previous interval

## Hypotheses
* none

## Conclusion
* the inverse of the difference keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_minus_` is sound for `-`. -/
theorem SyntaxTree.minus_sound (prev₁ prev₂ : Dom) :
    BinarySound Binary.minus.fn prev₁ prev₂ (Real.Interval.minus prev₁ prev₂)
      funHanMinus := by -- --- PROOF ---
  intro int _ s₁ s₂ h₁ h₂ hi
  simp only [Binary.fn, funHanMinus, Dom.contains, Dom.within, Real.Interval.intersection,
    Real.Interval.minus, Real.Interval.plus, Pi.sub_apply, Pi.add_apply] at *
  refine ⟨⟨max_le h₁.1 (by linarith [hi.1, h₂.1]), le_min h₁.2 (by linarith [hi.2, h₂.2])⟩,
    ⟨max_le h₂.1 (by linarith [hi.2, h₁.1]), le_min h₂.2 (by linarith [hi.1, h₁.2])⟩,
    ⟨le_max_left _ _, min_le_left _ _⟩, ⟨le_max_left _ _, min_le_left _ _⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

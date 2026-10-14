module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_minus_`: the contraction of a difference

`aux_minus_(int,intPrev1,intPrev2)` of `syntaxTree.m`: from `x₁ - x₂ ∈ int`, `x₁ ∈ int + intPrev2`
and
`x₂ ∈ intPrev1 - int`, each met with the operand's own interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_minus_`: `intPrev1 & (int + intPrev2)` and `intPrev2 & (intPrev1 - int)`. -/
noncomputable def SyntaxTree.funHanMinus (int prev₁ prev₂ : Dom) : Pair :=
  ⟨Real.Interval.intersection prev₁ (Real.Interval.plus int prev₂),
    Real.Interval.intersection prev₂ (Real.Interval.minus prev₁ int)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

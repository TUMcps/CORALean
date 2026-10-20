module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_plus_`: the contraction of a sum

`aux_plus_(int,intPrev1,intPrev2)` of `syntaxTree.m`: from `x₁ + x₂ ∈ int`, `x₁ ∈ int - intPrev2`
and `x₂ ∈ int - intPrev1`, each met with the operand's own interval. A numeric operand is a point
interval; CORA returns `[]` for it, and the node uses only the other component.

## Inputs
* `int` – target interval
* `prev₁` – first previous interval
* `prev₂` – second previous interval

## Output
* the intervals of both operands of a sum
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_plus_`: `intPrev1 & (int - intPrev2)` and `intPrev2 & (int - intPrev1)`. -/
noncomputable def SyntaxTree.funHanPlus (int prev₁ prev₂ : Dom) : Pair :=
  ⟨Real.Interval.intersection prev₁ (Real.Interval.minus int prev₂),
    Real.Interval.intersection prev₂ (Real.Interval.minus int prev₁)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

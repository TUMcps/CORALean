module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `backpropagation`: contracting a box with a syntax tree

`backpropagation(obj,value,int)` of `syntaxTree.m`: a variable leaf narrows its coordinate of the
box to `value & int(id)` (throwing `CORA:emptySet` if they do not meet); a node asks its `funHan`
for the interval each operand must take, narrows the box by each, and a binary node meets the two
boxes. The errors `CORA:emptySet` and `CORA:outOfDomain` are `Outcome.emptySet` and
`Outcome.outOfDomain`, the first operand's first; a numeric operand is a point interval.
Real-only, a specification: it narrows a box of real numbers exactly; its rounded refinement is
`SyntaxTree.backpropagationFloat`.

## Inputs
* none

## Output
* the box narrowed to where the tree takes the value, or an empty outcome
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `backpropagation(obj,value,int)`: the box `int` narrowed to where `obj` can take `value`. -/
noncomputable def SyntaxTree.backpropagation :
    SyntaxTree n → Dom → Real.Interval (Vec ℝ n) → Outcome (Real.Interval (Vec ℝ n))
  | .var i _, value, int =>
    -- check if node is base variable or not
    if ¬ (max (value.inf 0) (int.inf i) ≤ min (value.sup 0) (int.sup i)) ∨ value.sup 0 < value.inf 0
    then .emptySet
    else .ok ⟨Function.update int.inf i (max (value.inf 0) (int.inf i)),
      Function.update int.sup i (min (value.sup 0) (int.sup i))⟩
  | .unary _ _ funHan obj, value, int =>
    -- tighten interval
    match funHan value obj.value with
    | .ok val => backpropagation obj val int
    | .emptySet => .emptySet
    | .outOfDomain => .outOfDomain
  | .binary _ _ funHan obj₁ obj₂, value, int =>
    -- tighten interval
    let ⟨val₁, val₂⟩ := funHan value obj₁.value obj₂.value
    match backpropagation obj₁ val₁ int with
    | .ok res₁ =>
      match backpropagation obj₂ val₂ int with
      | .ok res₂ => .ok (Real.Interval.intersection res₁ res₂)
      | .emptySet => .emptySet
      | .outOfDomain => .outOfDomain
    | .emptySet => .emptySet
    | .outOfDomain => .outOfDomain
  | .numLeft _ _ funHan c obj, value, int =>
    let ⟨_, val⟩ := funHan value (interval c c) obj.value
    backpropagation obj val int
  | .numRight _ _ funHan obj c, value, int =>
    let ⟨val, _⟩ := funHan value obj.value (interval c c)
    backpropagation obj val int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

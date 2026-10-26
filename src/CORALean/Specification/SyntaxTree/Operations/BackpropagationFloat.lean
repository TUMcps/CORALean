module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat
public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat

@[expose] public section

/-!
# `backpropagation`: contracting a box with a float syntax tree

`backpropagation(obj,value,int)` of `syntaxTree.m` with the bounds held in `𝕋`: a variable leaf
narrows its coordinate of the box to `value & int(id)` (`CORA:emptySet` where the two are certified
apart); a node asks its `funHan` for the interval of each operand, narrows the box by each, and a
binary node meets the two boxes, exactly. A numeric operand is a point interval. Soundness is
`SyntaxTree.backpropagationFloat_sound`.

## Inputs
* none

## Output
* the box narrowed to where the tree takes the value, or an empty outcome
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `backpropagation(obj,value,int)`: the box `int` narrowed to where `obj` can take `value`. -/
def SyntaxTree.backpropagationFloat :
    Float.SyntaxTree 𝕋 n → Float.SyntaxTree.Dom 𝕋 → Float.Interval (Vec 𝕋 n) →
      SyntaxTree.Outcome (Float.Interval (Vec 𝕋 n))
  | .var i _, value, int =>
    -- check if node is base variable or not
    if ltStrict (minimum (value.sup 0) (int.sup i)) (maximum (value.inf 0) (int.inf i)) = true ∨
        ltStrict (value.sup 0) (value.inf 0) = true then .emptySet
    else .ok ⟨Function.update int.inf i (maximum (value.inf 0) (int.inf i)),
      Function.update int.sup i (minimum (value.sup 0) (int.sup i))⟩
  | .unary _ _ funHan obj, value, int =>
    -- tighten interval
    match funHan value obj.value with
    | .ok val => backpropagationFloat obj val int
    | .emptySet => .emptySet
    | .outOfDomain => .outOfDomain
  | .binary _ _ funHan obj₁ obj₂, value, int =>
    -- tighten interval
    let ⟨val₁, val₂⟩ := funHan value obj₁.value obj₂.value
    match backpropagationFloat obj₁ val₁ int with
    | .ok res₁ =>
      match backpropagationFloat obj₂ val₂ int with
      | .ok res₂ => .ok (Float.Interval.intersection res₁ res₂)
      | .emptySet => .emptySet
      | .outOfDomain => .outOfDomain
    | .emptySet => .emptySet
    | .outOfDomain => .outOfDomain
  | .numLeft _ _ funHan c obj, value, int =>
    let ⟨_, val⟩ := funHan value (SyntaxTree.intervalFloat c c) obj.value
    backpropagationFloat obj val int
  | .numRight _ _ funHan obj c, value, int =>
    let ⟨val, _⟩ := funHan value obj.value (SyntaxTree.intervalFloat c c)
    backpropagationFloat obj val int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

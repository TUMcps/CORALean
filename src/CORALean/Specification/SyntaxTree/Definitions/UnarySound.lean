module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# A sound unary `funHan

`funHan` of a unary node is sound for the function `f` of the node when, for a target `int` inside
the
node's own interval `v`, every `s` of the operand's interval `prev` with `f s ∈ int` survives:
`funHan`
does not throw, and returns an interval that holds `s` and lies inside `prev`.

## Inputs
* `f` – unary function
* `prev` – previous interval
* `v` – value interval
* `funHan` – backpropagation of the function

## Output
* the backpropagation keeps every solution inside the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `funHan` keeps every solution `s ∈ prev` of `f s ∈ int`, for a target `int` inside `v`. -/
def SyntaxTree.UnarySound (f : ℝ → ℝ) (prev v : Dom)
    (funHan : Dom → Dom → Outcome Dom) : Prop :=
  ∀ int : Dom, Dom.within int v → ∀ s, Dom.contains prev s → Dom.contains int (f s) →
    ∃ val, funHan int prev = .ok val ∧ Dom.contains val s ∧ Dom.within val prev

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

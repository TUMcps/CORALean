module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# A sound unary `funHan` over float intervals

`IsUnarySound` for the float intervals of `Float.SyntaxTree`: for a target `int` inside the node's
own interval `v`, every `s` of the operand's interval `prev` with `f s ∈ int` survives, the bounds
read as reals. `funHan` does not throw, and returns an interval that holds `s` and lies inside
`prev`.

## Inputs
* `f` – unary function
* `prev` – previous interval
* `v` – value interval
* `funHan` – backpropagation of the function

## Output
* the backpropagation keeps every solution inside the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `funHan` keeps every solution `s ∈ prev` of `f s ∈ int`, for a target `int` inside `v`. -/
def SyntaxTree.IsUnarySoundFloat (f : ℝ → ℝ) (prev v : Float.SyntaxTree.Dom 𝕋)
    (funHan : Float.SyntaxTree.Dom 𝕋 → Float.SyntaxTree.Dom 𝕋 →
      SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋)) : Prop :=
  ∀ int : Float.SyntaxTree.Dom 𝕋, int.IsWithin v → ∀ s, prev.contains s → int.contains (f s) →
    ∃ val, funHan int prev = .ok val ∧ val.contains s ∧ val.IsWithin prev

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

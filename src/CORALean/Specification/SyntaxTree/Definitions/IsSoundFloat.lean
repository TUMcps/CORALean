module

public import CORALean.Specification.SyntaxTree.Definitions.IsBinarySoundFloat
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySoundFloat
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat

@[expose] public section

/-!
# A float syntax tree built for a box

`IsSound` for `Float.SyntaxTree`: every node of `t` stores an interval that encloses its function
over the float box `B`, read as reals, and has a `funHan` that is sound for it. A variable leaf
holds its coordinate, a numeric operand is the interval of its number.

## Inputs
* `n` – number of variables
* `B` – box of the variables

## Output
* every node holds its function over the box and has a sound backpropagation
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

/-- Every node holds its function over `B` and has a sound `funHan`. -/
def SyntaxTree.IsSoundFloat {n : ℕ} (B : Float.Interval (Vec 𝕋 n)) :
    Float.SyntaxTree 𝕋 n → Prop
  | .var i v => ∀ x, Float.SyntaxTree.IsInBox B x → v.contains (x i)
  | .unary op v h t => IsSoundFloat B t ∧
      (∀ x, Float.SyntaxTree.IsInBox B x → v.contains (op.fn (t.eval x))) ∧
      SyntaxTree.IsUnarySoundFloat op.fn t.value v h
  | .binary op v h t₁ t₂ => IsSoundFloat B t₁ ∧ IsSoundFloat B t₂ ∧
      (∀ x, Float.SyntaxTree.IsInBox B x → v.contains (op.fn (t₁.eval x) (t₂.eval x))) ∧
      SyntaxTree.IsBinarySoundFloat op.fn t₁.value t₂.value v h
  | .numLeft op v h c t => IsSoundFloat B t ∧
      (∀ x, Float.SyntaxTree.IsInBox B x → v.contains (op.fn (toReal c) (t.eval x))) ∧
      SyntaxTree.IsBinarySoundFloat op.fn (SyntaxTree.intervalFloat c c) t.value v h
  | .numRight op v h t c => IsSoundFloat B t ∧
      (∀ x, Float.SyntaxTree.IsInBox B x → v.contains (op.fn (t.eval x) (toReal c))) ∧
      SyntaxTree.IsBinarySoundFloat op.fn t.value (SyntaxTree.intervalFloat c c) v h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.SyntaxTree.Definitions.IsBinarySound
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# A syntax tree built for a box

`IsSound B t` holds when every node of `t` stores an interval that encloses its function over the
box `B` and has a `funHan` that is sound for it. The nodes the constructors of `syntaxTree.m` build
are sound under the domain conditions of their operator (`sound_exp`, ...), except `sinhCora` and
`tanCora`, whose printed `funHan` is not (`sinhCora_counterexample`, `tanCora_counterexample`).

## Inputs
* `n` – number of variables
* `B` – box of the variables

## Output
* every node holds its function over the box and has a sound backpropagation
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every node holds its function over `B` and has a sound `funHan`. -/
def SyntaxTree.IsSound {n : ℕ} (B : Real.Interval (Vec ℝ n)) : SyntaxTree n → Prop
  | .var i v => ∀ x, IsInBox B x → Dom.contains v (x i)
  | .unary op v h t => IsSound B t ∧ (∀ x, IsInBox B x → Dom.contains v (op.fn (t.eval x))) ∧
      IsUnarySound op.fn t.value v h
  | .binary op v h t₁ t₂ => IsSound B t₁ ∧ IsSound B t₂ ∧
      (∀ x, IsInBox B x → Dom.contains v (op.fn (t₁.eval x) (t₂.eval x))) ∧
      IsBinarySound op.fn t₁.value t₂.value v h
  | .numLeft op v h c t => IsSound B t ∧ (∀ x, IsInBox B x → Dom.contains v (op.fn c (t.eval x))) ∧
      IsBinarySound op.fn (interval c c) t.value v h
  | .numRight op v h t c => IsSound B t ∧ (∀ x, IsInBox B x → Dom.contains v (op.fn (t.eval x) c)) ∧
      IsBinarySound op.fn t.value (interval c c) v h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

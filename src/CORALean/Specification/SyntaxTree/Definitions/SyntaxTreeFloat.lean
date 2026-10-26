module

public import CORALean.Specification.SyntaxTree.Definitions.DomFloat
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# CORA's `syntaxTree` over a float scalar

The tree of `SyntaxTree` with the intervals and numbers it stores held in `𝕋` rather than ℝ: every
node carries the `Interval` of floats enclosing its value over the box and the `funHan` narrowing
its operand's interval. The `operator`s, their functions and the `Outcome` of a `funHan` are the
exact layer's. `eval` is the function a tree denotes, reading the stored numbers as reals. Intervals
are one-dimensional, with no infinite bound.

## Inputs
* `𝕋` – scalar of the stored bounds
* `n` – number of variables

## Output
* the tree, with the interval of each node and the value it denotes at a point

## References

None: CORA's `syntaxTree.m` cites no source. The CORA manual (v2026, Table 29) cites Jaulin et al.,
*Applied Interval Analysis*, Ch. 4.2.4, for the forward-backward contractor, a book that was not
read.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic


-- ========================================  MAIN TYPE  ========================================= --

/-- The two intervals a binary `funHan` returns, one for each operand. -/
structure SyntaxTree.Pair (𝕋 : Type) where
  left : SyntaxTree.Dom 𝕋
  right : SyntaxTree.Dom 𝕋

/-- What a unary `funHan` is: the target and previous intervals to an `Outcome`. -/
abbrev SyntaxTree.UnaryHan (𝕋 : Type) :=
  SyntaxTree.Dom 𝕋 → SyntaxTree.Dom 𝕋 → CORALean.SyntaxTree.Outcome (SyntaxTree.Dom 𝕋)

/-- What a binary `funHan` is: the target and the two previous intervals to a `Pair`. -/
abbrev SyntaxTree.BinaryHan (𝕋 : Type) :=
  SyntaxTree.Dom 𝕋 → SyntaxTree.Dom 𝕋 → SyntaxTree.Dom 𝕋 → SyntaxTree.Pair 𝕋

/-- A syntax tree of a function of `n` variables for forward-backward contraction, its nodes holding
float intervals. -/
inductive SyntaxTree (𝕋 : Type) (n : ℕ)
  | var (id : Fin n) (value : SyntaxTree.Dom 𝕋)
  | unary (operator : CORALean.SyntaxTree.Unary) (value : SyntaxTree.Dom 𝕋)
      (funHan : SyntaxTree.UnaryHan 𝕋) (node : SyntaxTree 𝕋 n)
  | binary (operator : CORALean.SyntaxTree.Binary) (value : SyntaxTree.Dom 𝕋)
      (funHan : SyntaxTree.BinaryHan 𝕋) (node₁ node₂ : SyntaxTree 𝕋 n)
  | numLeft (operator : CORALean.SyntaxTree.Binary) (value : SyntaxTree.Dom 𝕋)
      (funHan : SyntaxTree.BinaryHan 𝕋) (number : 𝕋) (node₂ : SyntaxTree 𝕋 n)
  | numRight (operator : CORALean.SyntaxTree.Binary) (value : SyntaxTree.Dom 𝕋)
      (funHan : SyntaxTree.BinaryHan 𝕋) (node₁ : SyntaxTree 𝕋 n) (number : 𝕋)

/-- The value of a tree at a point `x`: the function it denotes, its numbers read as reals. -/
noncomputable def SyntaxTree.eval {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} :
    SyntaxTree 𝕋 n → (Fin n → ℝ) → ℝ
  | .var i _, x => x i
  | .unary op _ _ t, x => op.fn (t.eval x)
  | .binary op _ _ t₁ t₂, x => op.fn (t₁.eval x) (t₂.eval x)
  | .numLeft op _ _ c t, x => op.fn (toReal c) (t.eval x)
  | .numRight op _ _ t c, x => op.fn (t.eval x) (toReal c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

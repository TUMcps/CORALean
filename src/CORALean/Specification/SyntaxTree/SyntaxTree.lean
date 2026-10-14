module

public import CORALean.Specification.SyntaxTree.Definitions.Dom
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-!
# CORA's `syntaxTree`: an expression for forward-backward contraction

`specification/syntaxTree.m`: the tree `contractForwardBackward` (hence `levelSet.tightenDomain`)
builds from a function of the variables, to narrow a box to the points where the function can
take a given value. It has nothing to do with the formulas of `stl`: `STL.Expr` is a predicate's
expression, evaluated at a point; a `syntaxTree` carries, at every node, the `interval` that
encloses its value over the box (`value`) and the `funHan` that, given an interval of values the
node must take, narrows the interval of its operand.

A leaf is a variable (`id`) holding its coordinate of the box, a node an `operator` (here the
function it stands for, `fn`), its `value`, its `funHan` and its operands (`nodes`), a number being
a numeric operand. `eval` is the function a tree denotes. Intervals are one-dimensional real-layer
`Interval`s: no infinite bound, and the `nodes` of CORA's array-valued trees are lists of trees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What a `funHan` returns: an interval, or one of the two errors it can throw. -/
inductive SyntaxTree.Outcome (α : Type)
  | ok (a : α)
  | emptySet
  | outOfDomain

/-- The two intervals a binary `funHan` returns, one for each operand. -/
structure SyntaxTree.Pair where
  first : SyntaxTree.Dom
  second : SyntaxTree.Dom

/-- The unary `operator`s; `power` carries its exponent. -/
inductive SyntaxTree.Unary
  | power (k : ℕ)
  | exp
  | log
  | sqrt
  | sin
  | cos
  | tan
  | asin
  | acos
  | atan
  | sinh
  | cosh
  | tanh
  | asinh
  | acosh
  | atanh
  | uminus

/-- The binary `operator`s: `'+'`, `'-'` and `'*'`. -/
inductive SyntaxTree.Binary
  | plus
  | minus
  | times

inductive SyntaxTree (n : ℕ)
  | var (id : Fin n) (value : SyntaxTree.Dom)
  | unary (operator : SyntaxTree.Unary) (value : SyntaxTree.Dom)
      (funHan : SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Outcome SyntaxTree.Dom)
      (node : SyntaxTree n)
  | binary (operator : SyntaxTree.Binary) (value : SyntaxTree.Dom)
      (funHan : SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Pair)
      (node₁ node₂ : SyntaxTree n)
  | numLeft (operator : SyntaxTree.Binary) (value : SyntaxTree.Dom)
      (funHan : SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Pair)
      (number : ℝ) (node₂ : SyntaxTree n)
  | numRight (operator : SyntaxTree.Binary) (value : SyntaxTree.Dom)
      (funHan : SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Dom → SyntaxTree.Pair)
      (node₁ : SyntaxTree n) (number : ℝ)

/-- The function an `operator` stands for. -/
noncomputable def SyntaxTree.Unary.fn : SyntaxTree.Unary → ℝ → ℝ
  | .power k, x => x ^ k
  | .exp, x => Real.exp x
  | .log, x => Real.log x
  | .sqrt, x => Real.sqrt x
  | .sin, x => Real.sin x
  | .cos, x => Real.cos x
  | .tan, x => Real.tan x
  | .asin, x => Real.arcsin x
  | .acos, x => Real.arccos x
  | .atan, x => Real.arctan x
  | .sinh, x => Real.sinh x
  | .cosh, x => Real.cosh x
  | .tanh, x => Real.tanh x
  | .asinh, x => Real.arsinh x
  | .acosh, x => Real.arcosh x
  | .atanh, x => Real.artanh x
  | .uminus, x => -x

/-- The function a binary `operator` stands for. -/
def SyntaxTree.Binary.fn : SyntaxTree.Binary → ℝ → ℝ → ℝ
  | .plus, x, y => x + y
  | .minus, x, y => x - y
  | .times, x, y => x * y

/-- `obj.value`: the interval a node stores. -/
def SyntaxTree.value {n : ℕ} : SyntaxTree n → SyntaxTree.Dom
  | .var _ v => v
  | .unary _ v _ _ => v
  | .binary _ v _ _ _ => v
  | .numLeft _ v _ _ _ => v
  | .numRight _ v _ _ _ => v

/-- The value of a tree at a point `x`: the function it denotes. -/
noncomputable def SyntaxTree.eval {n : ℕ} : SyntaxTree n → (Fin n → ℝ) → ℝ
  | .var i _, x => x i
  | .unary op _ _ t, x => op.fn (t.eval x)
  | .binary op _ _ t₁ t₂, x => op.fn (t₁.eval x) (t₂.eval x)
  | .numLeft op _ _ c t, x => op.fn c (t.eval x)
  | .numRight op _ _ t c, x => op.fn (t.eval x) c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

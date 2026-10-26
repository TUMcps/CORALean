module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# CORA's arithmetic expressions over the state

The non-logic `stl` objects of CORA (`@stl/plus.m`, `minus.m`, `times.m`, `power.m`): the variable
`x(i)`, a number, and sums, differences, products and integer powers of them, generic over the
type of the numbers (`STL.Expr 𝕋 n` at a float scalar). `eval` reads an expression over `ℝ` at a
state `x ∈ ℝⁿ`.

Not modelled: the nonlinear operators (`sin`, `exp`, ...), non-integer exponents (MATLAB's `.^` of
a negative base is complex there) and division by zero (`x^(-1)` at `0` is `Inf` in MATLAB, `0`
here).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- An arithmetic expression over the state: a variable, a number, and sums, differences, products
and integer powers. -/
inductive STL.Expr (κ : Type) (n : ℕ)
  | var (i : Fin n)
  | num (c : κ)
  | add (e₁ e₂ : Expr κ n)
  | sub (e₁ e₂ : Expr κ n)
  | mul (e₁ e₂ : Expr κ n)
  | pow (e : Expr κ n) (k : ℤ)

/-- The value of an expression at the state `x`. -/
noncomputable def STL.Expr.eval {n : ℕ} : STL.Expr ℝ n → (Fin n → ℝ) → ℝ
  | .var i, x => x i
  | .num c, _ => c
  | .add e₁ e₂, x => e₁.eval x + e₂.eval x
  | .sub e₁ e₂, x => e₁.eval x - e₂.eval x
  | .mul e₁ e₂, x => e₁.eval x * e₂.eval x
  | .pow e k, x => e.eval x ^ k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

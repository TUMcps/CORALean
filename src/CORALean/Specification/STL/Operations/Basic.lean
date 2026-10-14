module

public import CORALean.Specification.STL.Operations.CmpNegate
public import CORALean.Specification.STL.Operations.TreeCompare
public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Operations.TreeNnfWith

@[expose] public section

/-!
# `STL/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  `STL.Expr.minus`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `minus.m`: the difference node, whichever operand is the number. -/
def STL.Expr.minus (e₁ e₂ : STL.Expr n) : STL.Expr n := .sub e₁ e₂

end CORALean


-- =====================================  `STL.Expr.plus`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `plus.m`: the sum node, a numeric left operand moved to the right. -/
def STL.Expr.plus : STL.Expr n → STL.Expr n → STL.Expr n
  | .num c, e₂ => .add e₂ (.num c)
  | e₁, e₂ => .add e₁ e₂

end CORALean


-- =====================================  `STL.Expr.power`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `power.m`: the power node, of an `stl` operand and a number. -/
def STL.Expr.power (e : STL.Expr n) (k : ℤ) : STL.Expr n := .pow e k

end CORALean


-- =====================================  `STL.Expr.times`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `times.m`: the product node, the numeric operand first. -/
def STL.Expr.times : STL.Expr n → STL.Expr n → STL.Expr n
  | .num c, e₂ => .mul (.num c) e₂
  | e₁, .num c => .mul (.num c) e₁
  | e₁, e₂ => .mul e₂ e₁

end CORALean


-- ==============================  `STL.Tree.eliminateTrueFalse`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `eliminateTrueFalse(obj)`, keeping `φ U[a,b] true`, which is not `true` in general. -/
def STL.Tree.eliminateTrueFalse (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.eliminateTrueFalseWith (fun a b φ => .until a b φ .tt) φ

end CORALean


-- ======================================  `STL.Tree.ge`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `ge.m`: the node of `e₁ >= e₂`. -/
def STL.Tree.ge (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .ge e₁ e₂

end CORALean


-- ======================================  `STL.Tree.gt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `gt.m`: the node of `e₁ > e₂`. -/
def STL.Tree.gt (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .gt e₁ e₂

end CORALean


-- ====================================  `STL.Tree.implies`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `implies.m`: the node `~φ | ψ`. -/
def STL.Tree.implies (φ ψ : STL.Tree n) : STL.Tree n := .or (.not φ) ψ

end CORALean


-- ======================================  `STL.Tree.le`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `le.m`: the node of `e₁ <= e₂`. -/
def STL.Tree.le (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .le e₁ e₂

end CORALean


-- ======================================  `STL.Tree.lt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `lt.m`: the node of `e₁ < e₂`. -/
def STL.Tree.lt (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .lt e₁ e₂

end CORALean


-- ==============================  `STL.Tree.negationNormalForm`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `negationNormalForm(obj)`, a negated comparison becoming the comparison that fails. -/
def STL.Tree.negationNormalForm (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.nnfWith STL.Cmp.negate false φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

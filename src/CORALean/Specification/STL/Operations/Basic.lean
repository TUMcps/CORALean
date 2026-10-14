module

public import CORALean.Specification.STL.Operations.CmpNegate
public import CORALean.Specification.STL.Operations.TreeAssignIdentifiersFrom
public import CORALean.Specification.STL.Operations.TreeCompare
public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Operations.TreeMaximumTimeFrom
public import CORALean.Specification.STL.Operations.TreeMinimumTimeFrom
public import CORALean.Specification.STL.Operations.TreeNnfWith

@[expose] public section

/-!
# `STL/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  `STL.Expr.minus`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus.m`: the difference node, whichever operand is the number. -/
def STL.Expr.minus (e₁ e₂ : STL.Expr n) : STL.Expr n := .sub e₁ e₂


-- =====================================  `STL.Expr.plus`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus.m`: the sum node, a numeric left operand moved to the right. -/
def STL.Expr.plus : STL.Expr n → STL.Expr n → STL.Expr n
  | .num c, e₂ => .add e₂ (.num c)
  | e₁, e₂ => .add e₁ e₂


-- =====================================  `STL.Expr.power`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power.m`: the power node, of an `stl` operand and a number. -/
def STL.Expr.power (e : STL.Expr n) (k : ℤ) : STL.Expr n := .pow e k


-- =====================================  `STL.Expr.times`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times.m`: the product node, the numeric operand first. -/
def STL.Expr.times : STL.Expr n → STL.Expr n → STL.Expr n
  | .num c, e₂ => .mul (.num c) e₂
  | e₁, .num c => .mul (.num c) e₁
  | e₁, e₂ => .mul e₂ e₁


-- ===============================  `STL.Tree.assignIdentifiers`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `assignIdentifiers(obj)`: the numbered non-temporal sub-formulas, the second output. -/
def STL.Tree.assignIdentifiers (φ : STL.Tree n) : List (STL.Tree n) := φ.assignIdentifiersFrom []


-- ==============================  `STL.Tree.eliminateTrueFalse`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eliminateTrueFalse(obj)`, keeping `φ U[a,b] true`, which is not `true` in general. -/
def STL.Tree.eliminateTrueFalse (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.eliminateTrueFalseWith (fun a b φ => .until a b φ .tt) φ


-- ======================================  `STL.Tree.ge`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ge.m`: the node of `e₁ >= e₂`. -/
def STL.Tree.ge (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .ge e₁ e₂


-- =================================  `STL.Tree.getClausesCnf`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_getClausesCNF(obj)`: the conjuncts of `obj`, split at every `&`. -/
def STL.Tree.getClausesCnf : STL.Tree n → List (STL.Tree n)
  | .and φ ψ => φ.getClausesCnf ++ ψ.getClausesCnf
  | φ => [φ]


-- =================================  `STL.Tree.getClausesDnf`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_getClausesDNF(obj)`: the disjuncts of `obj`, split at every `|`. -/
def STL.Tree.getClausesDnf : STL.Tree n → List (STL.Tree n)
  | .or φ ψ => φ.getClausesDnf ++ ψ.getClausesDnf
  | φ => [φ]


-- ==================================  `STL.Tree.getClauses`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `getClauses(obj,type)`: `type` is `'cnf'` (`dnf = false`) or `'dnf'`. -/
def STL.Tree.getClauses (φ : STL.Tree n) (dnf : Bool := false) : List (STL.Tree n) :=
  if dnf then φ.getClausesDnf else φ.getClausesCnf


-- ======================================  `STL.Tree.gt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `gt.m`: the node of `e₁ > e₂`. -/
def STL.Tree.gt (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .gt e₁ e₂


-- ====================================  `STL.Tree.implies`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `implies.m`: the node `~φ | ψ`. -/
def STL.Tree.implies (φ ψ : STL.Tree n) : STL.Tree n := .or (.not φ) ψ


-- ==================================  `STL.Tree.isPredicate`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `isPredicate(obj)`: a conjunction of comparisons of expressions. -/
def STL.Tree.isPredicate : STL.Tree n → Bool
  | .cmp _ _ _ => true
  | .and φ ψ => φ.isPredicate && ψ.isPredicate
  | _ => false


-- ======================================  `STL.Tree.le`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le.m`: the node of `e₁ <= e₂`. -/
def STL.Tree.le (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .le e₁ e₂


-- ======================================  `STL.Tree.lt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `lt.m`: the node of `e₁ < e₂`. -/
def STL.Tree.lt (e₁ e₂ : STL.Expr n) : STL.Tree n := STL.Tree.compare .lt e₁ e₂


-- ==================================  `STL.Tree.maximumTime`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `maximumTime(obj)`: the latest time the formula looks at. -/
def STL.Tree.maximumTime (φ : STL.Tree n) : ℝ≥0 := φ.maximumTimeFrom 0


-- ==================================  `STL.Tree.minimumTime`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minimumTime(obj)`: a lower bound on the earliest time the formula looks at. -/
def STL.Tree.minimumTime (φ : STL.Tree n) : ℝ≥0 := φ.minimumTimeFrom 0


-- ==============================  `STL.Tree.negationNormalForm`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `negationNormalForm(obj)`, a negated comparison becoming the comparison that fails. -/
def STL.Tree.negationNormalForm (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.nnfWith STL.Cmp.negate false φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

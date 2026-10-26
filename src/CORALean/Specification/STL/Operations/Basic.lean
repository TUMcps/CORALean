module

public import CORALean.Specification.STL.Operations.CmpNegate
public import CORALean.Specification.STL.Operations.TreeAssignIdentifiersFrom
public import CORALean.Specification.STL.Operations.TreeCompare
public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Operations.TreeMaximumTimeFrom
public import CORALean.Specification.STL.Operations.TreeMaximumTimeFromFloat
public import CORALean.Specification.STL.Operations.TreeMinimumTimeFrom
public import CORALean.Specification.STL.Operations.TreeMinimumTimeFromFloat
public import CORALean.Specification.STL.Operations.TreeNnfWith
public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# `STL/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

The syntax-tree operations are generic over the types of the times and numbers (`STL.Tree τ κ n`),
read at a float scalar through `STL.Tree.toReal`; `maximumTime` and `minimumTime` state the exact
horizon of a real formula, bounded by `maximumTimeFloat` and `minimumTimeFloat`.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open scoped NNReal

variable {τ κ : Type} [Zero κ] {n : ℕ} {X : Type}


-- =====================================  `STL.Expr.minus`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus.m`: the difference node, whichever operand is the number. -/
def STL.Expr.minus (e₁ e₂ : STL.Expr κ n) : STL.Expr κ n := .sub e₁ e₂


-- =====================================  `STL.Expr.plus`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus.m`: the sum node, a numeric left operand moved to the right. -/
def STL.Expr.plus : STL.Expr κ n → STL.Expr κ n → STL.Expr κ n
  | .num c, e₂ => .add e₂ (.num c)
  | e₁, e₂ => .add e₁ e₂


-- =====================================  `STL.Expr.power`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power.m`: the power node, of an `stl` operand and a number. -/
def STL.Expr.power (e : STL.Expr κ n) (k : ℤ) : STL.Expr κ n := .pow e k


-- =====================================  `STL.Expr.times`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times.m`: the product node, the numeric operand first. -/
def STL.Expr.times : STL.Expr κ n → STL.Expr κ n → STL.Expr κ n
  | .num c, e₂ => .mul (.num c) e₂
  | e₁, .num c => .mul (.num c) e₁
  | e₁, e₂ => .mul e₂ e₁


-- ====================================  `STL.Formula.and`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `φ ∧ ψ`, by De Morgan. -/
def STL.Formula.and (φ ψ : STL.Formula X) : STL.Formula X := .not (.or (.not φ) (.not ψ))


-- =====================================  `STL.Formula.ff`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `false`. -/
def STL.Formula.ff : STL.Formula X := .atom fun _ => False


-- ===================================  `STL.Formula.bigOr`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `⋁` of a list, `false` for the empty one. -/
def STL.Formula.bigOr (l : List (STL.Formula X)) : STL.Formula X := l.foldr .or .ff


-- ==================================  `STL.Formula.implies`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `φ ⇒ ψ := ¬φ ∨ ψ`. -/
def STL.Formula.implies (φ ψ : STL.Formula X) : STL.Formula X := .or (.not φ) ψ


-- ==================================  `STL.Formula.release`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `φ R[a,b] ψ := ¬(¬φ U[a,b] ¬ψ)`. -/
def STL.Formula.release (a b : ℝ≥0) (φ ψ : STL.Formula X) : STL.Formula X :=
  .not (.until a b (.not φ) (.not ψ))


-- =====================================  `STL.Formula.tt`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `true`. -/
def STL.Formula.tt : STL.Formula X := .atom fun _ => True


-- ===================================  `STL.Formula.bigAnd`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `⋀` of a list, `true` for the empty one. -/
def STL.Formula.bigAnd (l : List (STL.Formula X)) : STL.Formula X := l.foldr .and .tt


-- ==================================  `STL.Formula.finally`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `F[a,b] φ := true U[a,b] φ`. -/
def STL.Formula.finally (a b : ℝ≥0) (φ : STL.Formula X) : STL.Formula X := .until a b .tt φ


-- ==================================  `STL.Formula.globally`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- `G[a,b] φ := ¬F[a,b] ¬φ`. -/
def STL.Formula.globally (a b : ℝ≥0) (φ : STL.Formula X) : STL.Formula X :=
  .not (.finally a b (.not φ))


-- ====================================  `STL.Formula.next`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---

/-- The continuous next-operator `Xₐ φ := true U[a,a] φ`. -/
def STL.Formula.next (a : ℝ≥0) (φ : STL.Formula X) : STL.Formula X := .until a a .tt φ


-- ===============================  `STL.Tree.assignIdentifiers`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `assignIdentifiers(obj)`: the numbered non-temporal sub-formulas, the second output. -/
def STL.Tree.assignIdentifiers (φ : STL.Tree τ κ n) : List (STL.Tree τ κ n) :=
  φ.assignIdentifiersFrom []


-- ==============================  `STL.Tree.eliminateTrueFalse`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `eliminateTrueFalse(obj)`, keeping `φ U[a,b] true`, which is not `true` in general. -/
def STL.Tree.eliminateTrueFalse (φ : STL.Tree τ κ n) : STL.Tree τ κ n :=
  STL.Tree.eliminateTrueFalseWith (fun a b φ => .until a b φ .tt) φ


-- ======================================  `STL.Tree.ge`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ge.m`: the node of `e₁ >= e₂`. -/
def STL.Tree.ge (e₁ e₂ : STL.Expr κ n) : STL.Tree τ κ n := STL.Tree.compare .ge e₁ e₂


-- =================================  `STL.Tree.getClausesCnf`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_getClausesCNF(obj)`: the conjuncts of `obj`, split at every `&`. -/
def STL.Tree.getClausesCnf : STL.Tree τ κ n → List (STL.Tree τ κ n)
  | .and φ ψ => φ.getClausesCnf ++ ψ.getClausesCnf
  | φ => [φ]


-- =================================  `STL.Tree.getClausesDnf`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_getClausesDNF(obj)`: the disjuncts of `obj`, split at every `|`. -/
def STL.Tree.getClausesDnf : STL.Tree τ κ n → List (STL.Tree τ κ n)
  | .or φ ψ => φ.getClausesDnf ++ ψ.getClausesDnf
  | φ => [φ]


-- ==================================  `STL.Tree.getClauses`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `getClauses(obj,type)`: `type` is `'cnf'` (`dnf = false`) or `'dnf'`. -/
def STL.Tree.getClauses (φ : STL.Tree τ κ n) (dnf : Bool := false) : List (STL.Tree τ κ n) :=
  if dnf then φ.getClausesDnf else φ.getClausesCnf


-- ======================================  `STL.Tree.gt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `gt.m`: the node of `e₁ > e₂`. -/
def STL.Tree.gt (e₁ e₂ : STL.Expr κ n) : STL.Tree τ κ n := STL.Tree.compare .gt e₁ e₂


-- ====================================  `STL.Tree.implies`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `implies.m`: the node `~φ | ψ`. -/
def STL.Tree.implies (φ ψ : STL.Tree τ κ n) : STL.Tree τ κ n := .or (.not φ) ψ


-- ==================================  `STL.Tree.isPredicate`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `isPredicate(obj)`: a conjunction of comparisons of expressions. -/
def STL.Tree.isPredicate : STL.Tree τ κ n → Bool
  | .cmp _ _ _ => true
  | .and φ ψ => φ.isPredicate && ψ.isPredicate
  | _ => false


-- ======================================  `STL.Tree.le`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le.m`: the node of `e₁ <= e₂`. -/
def STL.Tree.le (e₁ e₂ : STL.Expr κ n) : STL.Tree τ κ n := STL.Tree.compare .le e₁ e₂


-- ======================================  `STL.Tree.lt`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `lt.m`: the node of `e₁ < e₂`. -/
def STL.Tree.lt (e₁ e₂ : STL.Expr κ n) : STL.Tree τ κ n := STL.Tree.compare .lt e₁ e₂


-- ==================================  `STL.Tree.maximumTime`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `maximumTime(obj)`: the latest time the formula looks at. -/
def STL.Tree.maximumTime (φ : STL.Tree NNReal κ n) : ℝ≥0 := φ.maximumTimeFrom 0


-- ===============================  `STL.Tree.maximumTimeFloat`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `maximumTime(obj)` over floats: an upper bound of the latest time the formula looks at. -/
def STL.Tree.maximumTimeFloat {𝕋 : Type} [Float.FloatOps 𝕋] (φ : STL.Tree 𝕋 κ n) : 𝕋 :=
  φ.maximumTimeFromFloat Float.FloatOps.zero


-- ==================================  `STL.Tree.minimumTime`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minimumTime(obj)`: a lower bound on the earliest time the formula looks at. -/
def STL.Tree.minimumTime (φ : STL.Tree NNReal κ n) : ℝ≥0 := φ.minimumTimeFrom 0


-- ===============================  `STL.Tree.minimumTimeFloat`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minimumTime(obj)` over floats: a lower bound of the earliest time the formula looks at. -/
def STL.Tree.minimumTimeFloat {𝕋 : Type} [Float.FloatOps 𝕋] (φ : STL.Tree 𝕋 κ n) : 𝕋 :=
  φ.minimumTimeFromFloat Float.FloatOps.zero


-- ==============================  `STL.Tree.negationNormalForm`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `negationNormalForm(obj)`, a negated comparison becoming the comparison that fails. -/
def STL.Tree.negationNormalForm (φ : STL.Tree τ κ n) : STL.Tree τ κ n :=
  STL.Tree.nnfWith STL.Cmp.negate false φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

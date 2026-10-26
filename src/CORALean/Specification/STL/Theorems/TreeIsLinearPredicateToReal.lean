module

public import CORALean.Specification.STL.Operations.ExprMap
public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.ExprIsLinear
public import CORALean.Specification.STL.Operations.TreeIsLinearPredicate
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `isLinearPredicate` of a float syntax tree, read as reals

`isLinearPredicate` tests the shape of the comparisons only, so a tree is a linear predicate iff its
reading is.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the reading is a linear predicate iff the tree is
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {τ τ' κ κ' : Type} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `isLinear` of an expression and mapping its numbers. -/
private theorem aux_isLinear_map (g : κ → κ') (e : STL.Expr κ n) : -- --- CONCL ---
    (e.map g).isLinear = e.isLinear := by -- --- PROOF ---
  induction e with
  | var i => rfl
  | num c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp only [STL.Expr.map, STL.Expr.isLinear, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ => simp only [STL.Expr.map, STL.Expr.isLinear, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    cases e₁ <;> cases e₂ <;> simp only [STL.Expr.map, STL.Expr.isLinear] at ih₁ ih₂ ⊢ <;>
      simp [ih₁, ih₂]
  | pow e k ih => rfl

/-- `isLinearPredicate` and mapping the times and numbers. -/
private theorem aux_isLinearPredicate_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.map f g).isLinearPredicate = φ.isLinearPredicate := by
  induction φ <;> simp_all [STL.Tree.isLinearPredicate, STL.Tree.map, aux_isLinear_map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.isLinearPredicate_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.toReal.isLinearPredicate = φ.isLinearPredicate :=
  aux_isLinearPredicate_map _ _ φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

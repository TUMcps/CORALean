module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeNegationNormalFormMap

@[expose] public section

/-!
# `conjunctiveNormalForm` of a float syntax tree, read as reals

The conjunctive normal form is the negation normal form followed by the CNF loop, which move nodes
and read no time or number, so the normal form of the tree read as reals is the normal form of the
tree, read as reals.

## Inputs
* `φ` – formula
* `nnf` – whether `φ` is in negation normal form already

## Hypotheses
* none

## Conclusion
* the result read as reals is the operation on the argument read as reals
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

set_option maxHeartbeats 400000 in -- 1331 constructor cases of the three matched operands
/-- One `cnf` pass and mapping the times and numbers. -/
private theorem aux_cnfRewrite_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) : -- --- CONCL ---
    (φ.map f g).cnfRewrite = ((φ.cnfRewrite).1.map f g, (φ.cnfRewrite).2) := by -- --- PROOF ---
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.cnfRewrite, STL.Tree.map, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.cnfRewrite, STL.Tree.map, ihφ, ihψ]
    generalize (φ.cnfRewrite).1 = l
    generalize (ψ.cnfRewrite).1 = r
    cases l <;> cases r <;> cases ψ <;> simp [STL.Tree.map]
  | _ => simp [STL.Tree.cnfRewrite, STL.Tree.map]

/-- The `cnf` loop and mapping the times and numbers. -/
private theorem aux_cnfLoop_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) : -- --- CONCL ---
    (φ.cnfLoop).map f g = (φ.map f g).cnfLoop := by -- --- PROOF ---
  fun_induction STL.Tree.cnfLoop φ with
  | case1 φ res cnt h =>
    -- nothing was rewritten, on the tree and on its mapping
    conv_rhs => rw [STL.Tree.cnfLoop, aux_cnfRewrite_map]
    simp [res, cnt, h]
  | case2 φ res cnt h ih =>
    -- something was rewritten: the loop continues on the rewritten tree
    conv_rhs => rw [STL.Tree.cnfLoop, aux_cnfRewrite_map]
    simp [res, cnt, h, ih]

/-- `conjunctiveNormalForm` and mapping the times and numbers. -/
private theorem aux_conjunctiveNormalForm_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n)
    (nnf : Bool) :
    (φ.conjunctiveNormalForm nnf).map f g = (φ.map f g).conjunctiveNormalForm nnf := by
  cases nnf <;> simp [STL.Tree.conjunctiveNormalForm, aux_cnfLoop_map,
    STL.Tree.negationNormalForm_map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.conjunctiveNormalForm_toReal (φ : STL.Tree 𝕋 𝕋 n) (nnf : Bool) :
    (φ.conjunctiveNormalForm nnf).toReal = φ.toReal.conjunctiveNormalForm nnf :=
  aux_conjunctiveNormalForm_map _ _ φ nnf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

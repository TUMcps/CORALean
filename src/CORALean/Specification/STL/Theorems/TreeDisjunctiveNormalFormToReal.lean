module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.TreeDisjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeDnfLoop
public import CORALean.Specification.STL.Operations.TreeDnfRewrite
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeNegationNormalFormMap

@[expose] public section

/-!
# `disjunctiveNormalForm` of a float syntax tree, read as reals

The disjunctive normal form is the negation normal form followed by the DNF loop, which move nodes
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
/-- One `dnf` pass and mapping the times and numbers. -/
private theorem aux_dnfRewrite_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) : -- --- CONCL ---
    (φ.map f g).dnfRewrite = ((φ.dnfRewrite).1.map f g, (φ.dnfRewrite).2) := by -- --- PROOF ---
  induction φ with
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.dnfRewrite, STL.Tree.map, ihφ, ihψ]
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.dnfRewrite, STL.Tree.map, ihφ, ihψ]
    generalize (φ.dnfRewrite).1 = l
    generalize (ψ.dnfRewrite).1 = r
    cases l <;> cases r <;> cases ψ <;> simp [STL.Tree.map]
  | _ => simp [STL.Tree.dnfRewrite, STL.Tree.map]

/-- The `dnf` loop and mapping the times and numbers. -/
private theorem aux_dnfLoop_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) : -- --- CONCL ---
    (φ.dnfLoop).map f g = (φ.map f g).dnfLoop := by -- --- PROOF ---
  fun_induction STL.Tree.dnfLoop φ with
  | case1 φ res cnt h =>
    -- nothing was rewritten, on the tree and on its mapping
    conv_rhs => rw [STL.Tree.dnfLoop, aux_dnfRewrite_map]
    simp [res, cnt, h]
  | case2 φ res cnt h ih =>
    -- something was rewritten: the loop continues on the rewritten tree
    conv_rhs => rw [STL.Tree.dnfLoop, aux_dnfRewrite_map]
    simp [res, cnt, h, ih]

/-- `disjunctiveNormalForm` and mapping the times and numbers. -/
private theorem aux_disjunctiveNormalForm_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n)
    (nnf : Bool) :
    (φ.disjunctiveNormalForm nnf).map f g = (φ.map f g).disjunctiveNormalForm nnf := by
  cases nnf <;> simp [STL.Tree.disjunctiveNormalForm, aux_dnfLoop_map,
    STL.Tree.negationNormalForm_map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.disjunctiveNormalForm_toReal (φ : STL.Tree 𝕋 𝕋 n) (nnf : Bool) :
    (φ.disjunctiveNormalForm nnf).toReal = φ.toReal.disjunctiveNormalForm nnf :=
  aux_disjunctiveNormalForm_map _ _ φ nnf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

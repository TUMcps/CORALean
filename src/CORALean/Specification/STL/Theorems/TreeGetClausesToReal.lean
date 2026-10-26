module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `getClauses` of a float syntax tree, read as reals

`getClauses` splits at every `&` or every `|`, which reads no time or number, so the clauses of the
tree read as reals are the clauses of the tree, read as reals.

## Inputs
* `φ` – formula
* `dnf` – whether the clauses are the disjuncts

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

/-- `getClausesCnf` and mapping the times and numbers. -/
private theorem aux_getClausesCnf_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    φ.getClausesCnf.map (STL.Tree.map f g) = (φ.map f g).getClausesCnf := by
  induction φ <;> simp_all [STL.Tree.getClausesCnf, STL.Tree.map]

/-- `getClausesDnf` and mapping the times and numbers. -/
private theorem aux_getClausesDnf_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    φ.getClausesDnf.map (STL.Tree.map f g) = (φ.map f g).getClausesDnf := by
  induction φ <;> simp_all [STL.Tree.getClausesDnf, STL.Tree.map]

/-- `getClauses` and mapping the times and numbers. -/
private theorem aux_getClauses_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) (dnf : Bool) :
    (φ.getClauses dnf).map (STL.Tree.map f g) = (φ.map f g).getClauses dnf := by
  cases dnf <;> simp [STL.Tree.getClauses, aux_getClausesCnf_map, aux_getClausesDnf_map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.getClauses_toReal (φ : STL.Tree 𝕋 𝕋 n) (dnf : Bool) :
    (φ.getClauses dnf).map STL.Tree.toReal = φ.toReal.getClauses dnf :=
  aux_getClauses_map _ _ φ dnf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.STL.Operations.TreeCompare

@[expose] public section

/-!
# A comparison node means the comparison

`lt`, `le`, `gt` and `ge` build a node that holds of a trace exactly when the comparison holds of
the two expressions at the state at time `0`, however the operands are swapped or subtracted.

## Inputs
* `op` – comparison
* `e₁` – left expression
* `e₂` – right expression
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the node holds iff the comparison holds at time zero
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_compare (op : STL.Cmp) (e₁ e₂ : STL.Expr n)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (STL.Tree.compare op e₁ e₂).Sat ξ ↔
      op.rel (e₁.eval (ξ 0)) (e₂.eval (ξ 0)) := by -- --- PROOF ---
  unfold STL.Tree.compare
  split
  · exact Iff.rfl
  · cases op <;> exact Iff.rfl
  · cases op <;> simp [STL.Tree.Sat, STL.Expr.eval, STL.Cmp.rel]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

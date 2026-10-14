module

public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Theorems.TreeIsCnfCnfRewrite

@[expose] public section

/-!
# The CNF loop ends in a conjunctive normal form

The loop stops at a pass that counts no distribution, and the result of such a pass is a
conjunction of clauses (`STL.Tree.isCnf_cnfRewrite_of_snd_eq_zero`).
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

theorem STL.Tree.isCnf_cnfLoop (φ : STL.Tree n) : φ.cnfLoop.IsCnf := by -- --- PROOF ---
  induction φ using STL.Tree.cnfLoop.induct with
  | case1 φ cnt hc =>
    rw [STL.Tree.cnfLoop, dif_pos hc]
    exact STL.Tree.isCnf_cnfRewrite_of_snd_eq_zero φ hc
  | case2 φ res cnt h ih => rw [STL.Tree.cnfLoop, dif_neg h]; exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

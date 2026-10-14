module

public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Theorems.TreeSatCnfRewrite

@[expose] public section

/-!
# The CNF loop keeps the meaning

Every pass keeps the satisfying traces (`STL.Tree.sat_cnfRewrite`), so the loop does.
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

theorem STL.Tree.sat_cnfLoop (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.cnfLoop.Sat ξ ↔ φ.Sat ξ := by
  induction φ using STL.Tree.cnfLoop.induct generalizing ξ with
  | case1 φ cnt hc => rw [STL.Tree.cnfLoop, dif_pos hc]; exact STL.Tree.sat_cnfRewrite φ ξ
  | case2 φ res cnt h ih =>
    rw [STL.Tree.cnfLoop, dif_neg h, ih, STL.Tree.sat_cnfRewrite]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

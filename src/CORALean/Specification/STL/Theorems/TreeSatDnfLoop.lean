module

public import CORALean.Specification.STL.Operations.TreeDnfLoop
public import CORALean.Specification.STL.Theorems.TreeSatDnfRewrite

@[expose] public section

/-!
# The DNF loop keeps the meaning

Every pass keeps the satisfying traces (`STL.Tree.sat_dnfRewrite`), so the loop does.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the loop keeps the meaning
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

theorem STL.Tree.sat_dnfLoop (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.dnfLoop.Sat ξ ↔ φ.Sat ξ := by
  induction φ using STL.Tree.dnfLoop.induct generalizing ξ with
  | case1 φ cnt hc => rw [STL.Tree.dnfLoop, dif_pos hc]; exact STL.Tree.sat_dnfRewrite φ ξ
  | case2 φ res cnt h ih =>
    rw [STL.Tree.dnfLoop, dif_neg h, ih, STL.Tree.sat_dnfRewrite]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

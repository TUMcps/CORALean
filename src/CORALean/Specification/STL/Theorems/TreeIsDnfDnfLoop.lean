module

public import CORALean.Specification.STL.Operations.TreeDnfLoop
public import CORALean.Specification.STL.Theorems.TreeIsDnfDnfRewrite

@[expose] public section

/-!
# The DNF loop ends in a disjunctive normal form

The loop stops at a pass that counts no distribution, and the result of such a pass is a
disjunction of cubes (`STL.Tree.isDnf_dnfRewrite_of_snd_eq_zero`).

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the loop result is in disjunctive normal form
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

theorem STL.Tree.isDnf_dnfLoop (φ : STL.Tree n) : -- --- CONCL ---
    φ.dnfLoop.IsDnf := by -- --- PROOF ---
  induction φ using STL.Tree.dnfLoop.induct with
  | case1 φ cnt hc =>
    rw [STL.Tree.dnfLoop, dif_pos hc]
    exact STL.Tree.isDnf_dnfRewrite_of_snd_eq_zero φ hc
  | case2 φ res cnt h ih => rw [STL.Tree.dnfLoop, dif_neg h]; exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

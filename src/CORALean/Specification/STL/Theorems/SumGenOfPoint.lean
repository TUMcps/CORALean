import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import Mathlib.Algebra.BigOperators.Fin

/-!
# A point has no weighted generators

`Zonotope.ofPoint v` of [1, Prop. 1] has no generators, so every sum indexed by them is `0`:
in particular a weighted sum of them.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem STL.sumGen_ofPoint (v : α) (F : Fin (Zonotope.ofPoint v).h → α) :
    ∑ k : Fin (Zonotope.ofPoint v).h, F k = 0 := by
  exact Finset.sum_eq_zero fun k => k.elim0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

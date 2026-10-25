module

public import CORALean.Global.Cost
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ExhaustiveSearchCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ExhaustiveSearchCostOpsLe

@[expose] public section

/-!
# `Zonotope.exhaustiveSearchCost_isBigO`

[1, Prop. 10]: for fixed `n`, the exhaustive search over `n` of `p` generators is
`O(C(p, n) · p)` in `p`.

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* search cost is `O(C(p, n) · p)` in the generator count

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems, 2010.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10]: for fixed `n`, the exhaustive search over `n` of `p` generators is
`O(C(p, n) · p)` in `p`. -/
theorem Zonotope.exhaustiveSearchCost_isBigO (n : ℕ) :
    (fun p : ℕ => ((Zonotope.exhaustiveSearchCost n p).ops : ℝ))
      =O[Filter.atTop] fun p : ℕ => ((p.choose n * p : ℕ) : ℝ) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop 1] with p hp
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast Zonotope.exhaustiveSearchCost_ops_le n p hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

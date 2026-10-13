import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError

/-!
# `Alg. 3` lines 3-7: the order-decrementing loop

Decrement the order while the reduction one step down still clears the share
`εSi`, and keep the last order that did — the loop `adaptSetOrder` drives, its
own file since [1]'s `Alg. 3` names it as a step in its own right.

Neither `Nat.find` nor `Classical.choose`, unlike `reduceBoxOrder` beside it:
`Z.h` decrements reach every order there is, so the bound is the set's own
size — unlike `Alg. 2`, whose step sweep has none.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-7: decrement the order while the reduction one step down still
clears the share, and keep the last order that did. -/
noncomputable def Zonotope.adaptSetOrderLoop (le : ℝ → ℝ → Bool)
    (Z : Zonotope (Vec ℝ n)) (εSi : ℝ) : ℕ → ℕ → ℕ
  | Φset, 0 => Φset
  | 0, _ + 1 => 0
  | Φset + 1, k + 1 =>
    if le (Z.reduceBoxError Φset) εSi then Zonotope.adaptSetOrderLoop le Z εSi Φset k else Φset + 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

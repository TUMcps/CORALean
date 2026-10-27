module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Which abstraction a nonlinear step uses

CORA's `options.alg` for `linReach`: `'lin'` linearizes and boxes the whole remainder,
`'poly'` keeps the second-order term over the start set as a polynomial [1].
`'linRem'` and the parameter variants are not offered.

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `options.alg`: `'lin'`, or `'poly'` with the order `options.errorOrder` the
start set is reduced to before its static error. -/
inductive NonlinearSys.LinReachAlg where
  | lin
  | poly (errorOrder : ℕ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

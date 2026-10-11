import CORALean.Global.Tensor
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic

/-!
# What [1, Alg. 3 (search)] carries from one iteration to the next

The variables of the `repeat` loop of `Alg. 3`: the counter `i`, the direction `ℓ_i`, the step
size `Δt` together with `k`, the number of steps of `Alg. 1` it takes to cover the time `t`
(halving `Δt` doubles `k`), the vertex lists of the polytopes `P̂` and `P̌`, and the flag
`falsifiable`. The polytopes are kept as the lists of the vertices their `conv` is taken of.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The loop variables of [1, Alg. 3 (search)] at the top of an iteration. -/
structure LinearSys.VerifySearchState (n : ℕ) where
  /-- `i`, line 1 and line 25: the number of directions tried since the last restart, plus one. -/
  i : ℕ
  /-- `ℓ_i`, lines 1 and 25. -/
  ℓ : Vec ℝ n →ₗ[ℝ] ℝ
  /-- `Δt`, lines 1 and 15. -/
  Δt : ℝ
  /-- The number of steps of `Δt` in `t`. -/
  k : ℕ
  /-- The vertices of `P̂`, lines 1, 11, 15 and 21. -/
  Phat : List (Vec ℝ n)
  /-- The vertices of `P̌`, lines 1, 11, 15 and 21. -/
  Pcheck : List (Vec ℝ n)
  /-- `falsifiable`, lines 1, 8 and 15. -/
  falsifiable : Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

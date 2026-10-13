import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Interval.Float.Interval

/-!
# State of the interval observer, in floats

CORA's `priv_observe_interval` [1, Alg. 1] carries four variables through its loop: the nominal
estimate `x`, the set `R_x` the initial error is mapped to, the box `R_wv` collecting the boxed
disturbance terms, and the disturbance set `D` mapped once more per step. At a float the nominal
estimate is not a point, since `A x + u + L (y - C x)` is not exact: it is the box that encloses
it.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.ObserveIntervalStateFloat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  x : Interval (Vec 𝕋 n)
  Rx : Zonotope (Vec 𝕋 n)
  Rwv : Interval (Vec 𝕋 n)
  D : Zonotope (Vec 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

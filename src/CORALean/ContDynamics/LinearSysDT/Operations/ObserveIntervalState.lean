import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStep
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# The interval observer's state after `k` steps

CORA's `priv_observe_interval` initialisation, `x = center(R0)`, `R_x = R0`, `R_wv = 0`,
`D = -L V + W`, then `observeIntervalStep` at the measurement `y k` and input `u k`.

[1, Alg. 1], lines 1-2 and the loop.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalState (sys : LinearSysDT ℝ n) (C : Mat ℝ p n) (L : Mat ℝ n p)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ p)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p) :
    ℕ → LinearSysDT.ObserveIntervalState n
  | 0 => { x := R₀.c, Rx := R₀, Rwv := Interval.point 0, D := (Zonotope.mtimes (-L) V).plus W }
  | k + 1 => sys.observeIntervalStep C L (u k) (y k) (sys.observeIntervalState C L R₀ W V u y k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

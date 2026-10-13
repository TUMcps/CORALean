import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# Options of the strip-based observer, in floats

CORA's `options` of `observe_stripBased` [2, Eq. 4], for the algorithm of [1, Alg. 1],
at the scalar `𝕋`: whether
the strips are taken one at a time (`sequential`), the gain as a function of the zonotope it
meets, and the order the observer's zonotope is reduced to. As at ℝ, no choice of gain is
modelled: the enclosure holds for every gain.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n p : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.ObserveStripOptionsFloat (𝕋 : Type) [FloatOps 𝕋] (n p : ℕ) where
  sequential : Bool
  gain : Zonotope (Vec 𝕋 n) → Mat 𝕋 n p
  zonotopeOrder : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

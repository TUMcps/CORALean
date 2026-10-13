import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Options of the strip-based observer

CORA's `options` for `observe_stripBased`: `intersectionType` 1 (the strips one at a time,
[1, Eq. 3]) or 2 (all at once), read here as `sequential`; `intersectionTechnique`, the gain,
read as a function of the zonotope the strips meet, so that an offline gain ([1, Eq. 9]) is a
constant and an online one (`'alamo-FRad'`, `'wang-FRad'`, ...) computes it from that zonotope;
and `ρ`, the order each step is reduced to. In the sequential case strip `i` takes
column `i` of the gain, evaluated at the zonotope it meets.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.ObserveStripOptions (n p : ℕ) where
  sequential : Bool
  gain : Zonotope (Vec ℝ n) → Mat ℝ n p
  ρ : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Global.Interfaces

@[expose] public section

/-!
# Options of the strip-based observer

CORA's `options` for `observe_stripBased`: `intersectionType` 1 (the strips one at a time,
[1, Eq. 3]) or 2 (all at once), read here as `sequential`; `intersectionTechnique`, the gain,
read as a function of the set the strips meet, so that an offline gain ([1, Eq. 9]) is a
constant and an online one (`'alamo-FRad'`, `'wang-FRad'`, ...) computes it from that set;
and `ρ`, the order each step is reduced to. In the sequential case strip `i` takes
column `i` of the gain, evaluated at the set it meets. At any scalar `𝕋` and set type `Z`: the
gain is a matrix of the scalar the observer computes in. No choice of gain is modelled: the
enclosure holds for every gain.

## References

* [1] [V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica,
      2013.](../../../../../references/2013/le-automatica-zonotopic-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The options of the strip-based observer: whether the strips are intersected one after the other,
the gain as a function of the zonotope, and the zonotope order `ρ`. -/
structure LinearSysDT.ObserveStripOptions (𝕋 Z : Type) (n p : ℕ) where
  sequential : Bool
  gain : Z → Mat 𝕋 n p
  ρ : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

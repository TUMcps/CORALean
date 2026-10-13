import CORALean.ContSet.Interval.Float.Interval

/-!
# `MatExp.halfSqBounds`, the factor `t²/2` between two floats

The `½ t²` of [1, Lemma 3.1], which a float cannot hold exactly: `mulDown`/`mulUp` of `t` with
itself bracket `t²`, and halving is exact, so the pair brackets `t²/2`. The one place
`expW` and `expIntervalW` both take it from.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Floats `(lo, hi)` bracketing `t² / 2`: the two directed squares, halved. -/
def MatExp.halfSqBounds (t : 𝕋) : 𝕋 × 𝕋 := (half (mulDown t t), half (mulUp t t))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

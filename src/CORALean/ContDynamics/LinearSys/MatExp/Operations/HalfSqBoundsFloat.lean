module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.halfSqBounds`, the factor `t²/2` between two floats

The `½ t²` of [1, Prop. 4], which a float cannot hold exactly: `mulDown`/`mulUp` of `t` with
itself bracket `t²`, and halving is exact, so the interval brackets `t²/2`. The one place
`expW` and `expIntervalW` both take it from.

## Inputs
* `t` – float time

## Output
* interval of floats bracketing half the square

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo, hi]` of floats bracketing `t² / 2`: the two directed squares, halved. -/
def MatExp.halfSqBounds (t : 𝕋) : Interval 𝕋 := ⟨half (mulDown t t), half (mulUp t t)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

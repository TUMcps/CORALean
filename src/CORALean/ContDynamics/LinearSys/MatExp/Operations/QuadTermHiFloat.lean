module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat

@[expose] public section

/-!
# The second-order Taylor term's diagonal factor, greatest value on a box, in floats

`quadTermHi`: `Real.MatExp.quadTermHi` of [1, Lemma 3.1] rounded up. The parabola opens
upwards, so the greatest value on `[a, b]` is at an endpoint, and the larger of the two endpoint
upper bounds is one.

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

/-- The greater of `γ`'s two endpoint upper bounds. -/
def MatExp.quadTermHi (t a b : 𝕋) : 𝕋 :=
  maximum (MatExp.quadTerm t a).sup (MatExp.quadTerm t b).sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

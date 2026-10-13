import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo

/-!
# The second-order Taylor term's diagonal factor, over a floating-point scalar

`quadTerm`: the `γ(a) = a t + ½ a² t²` of [1, Lemma 3.1] at a float `a`, as the interval
`γ` lies in. `a t` is bracketed by the two directed products and squared by the corner hull,
so the result rounds outward at every step.

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

/-- An interval holding `γ(a) = a t + ½ a² t²`, rounded outward. -/
def MatExp.quadTerm (t a : 𝕋) : Interval 𝕋 :=
  let mLo := mulDown a t                                            -- a t, from below
  let mHi := mulUp a t                                              -- a t, from above
  ⟨addDown mLo (half (Interval.mulLo mLo mHi mLo mHi)),             -- + ½ (a t)²
    addUp mHi (half (Interval.mulHi mLo mHi mLo mHi))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

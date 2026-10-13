import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat

/-!
# The second-order Taylor term's diagonal factor, least value on a box, in floats

`quadTermLo`: `Real.MatExp.quadTermLo` of [1, Lemma 3.1] rounded down. The vertex `-1/t`
cannot be held by a float, so the box is certified to lie on one side of it instead: `t + a t² > 0`
says `-1/t < a`, and `t + b t² < 0` says `b < -1/t`, each bounded outward. Failing both, `γ`'s
global floor `-1/2` is returned: sound where the box does straddle the vertex, and merely not
tight where the test was too close to call.

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

/-- A lower bound of `γ` on `[a, b]`: the lesser endpoint bound when the box is certified off
the vertex, `-1/2` otherwise. -/
def MatExp.quadTermLo (t a b : 𝕋) : 𝕋 :=
  let tSqLo := mulDown t t                                          -- t², from below
  let tSqHi := mulUp t t                                            -- t², from above
  let leftOfBox := addDown t (Interval.mulLo a a tSqLo tSqHi)       -- ≤ t + a t²
  let rightOfBox := addUp t (Interval.mulHi b b tSqLo tSqHi)        -- ≥ t + b t²
  if ltStrict zero leftOfBox || ltStrict rightOfBox zero then       -- -1/t < a, or b < -1/t
    minimum (MatExp.quadTerm t a).inf (MatExp.quadTerm t b).inf
  else neg (half one)                                               -- γ ≥ -1/2 everywhere

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

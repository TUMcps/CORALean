import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Operations.ConjCoeffsGap
import CORALean.NN.Layers.Operations.ConjTBound
import CORALean.NN.Layers.Operations.EvalPolyUp

/-!
# A polynomial relaxation carried along an affine conjugation

`g t = ra f (rb t) + c` inherits the relaxation of `f` read at the box `rb` maps `[l, u]` to. The
coefficients are rescaled and stored rounded up; the error is `ra` times `f`'s, rounded up, plus
what the coefficient roundings can move the polynomial by over the box, `max(|l|, |u|)` bounding
the argument.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g t = ra f (rb t) + c` inherits `f`'s polynomial relaxation. -/
def PolyRelaxation.ofAffineConj (P : PolyRelaxation 𝕋 m) (A B : ScaleRounding 𝕋) (c : 𝕋) :
    PolyRelaxation 𝕋 m where
  coeffs l u := conjCoeffsUp A B c (P.coeffs (B.down l) (B.up u))
  error l u :=
    addUp (A.up (P.error (B.down l) (B.up u)))
      (evalPolyUp (conjCoeffsGap A B c (P.coeffs (B.down l) (B.up u))) (Relaxation.conjTBound l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

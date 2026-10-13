import CORALean.NN.Layers.Operations.PowRange

/-!
# A polynomial evaluated from below

What a sample point needs of a fit: an enclosure of `Real.evalPoly` at the stored
coefficients, which is the whole of the fit's rounding. Interval arithmetic rather than
Horner, and sign is why: composing `mulUp x (mulUp …)` needs `0 ≤ x`, and no comparison of
stored values establishes a sign.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial the stored coefficients denote, from below. -/
def evalPolyDown (c : Fin (n + 1) → 𝕋) (t : 𝕋) : 𝕋 :=
  sumDown fun i => mulRangeDown (c i) (powRange t (i : ℕ)).1 (powRange t (i : ℕ)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Layers.Operations.PowRange

@[expose] public section

/-!
# A polynomial evaluated from below

What a sample point needs of a fit: an enclosure of `Real.evalPoly` at the stored
coefficients, which is the whole of the fit's rounding. Interval arithmetic rather than
Horner, and sign is why: composing `mulUp x (mulUp …)` needs `0 ≤ x`, and no comparison of
stored values establishes a sign.

## Inputs
* `c` – stored coefficients
* `t` – evaluation point

## Output
* lower bound of the polynomial's value
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial the stored coefficients denote, from below. -/
def evalPolyDown (c : Fin (n + 1) → 𝕋) (t : 𝕋) : 𝕋 :=
  sumDown fun i => mulRangeDown (c i) (powRange t (i : ℕ)).inf (powRange t (i : ℕ)).sup

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

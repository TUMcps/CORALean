module

public import CORALean.NN.Layers.Operations.PowRange

@[expose] public section

/-!
# A polynomial evaluated from above

The mirror of `evalPolyDown`, the same terms rounded the other way.

## Inputs
* `c` – stored coefficients
* `t` – evaluation point

## Output
* upper bound of the polynomial's value
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

/-- And from above, the same terms rounded the other way. -/
def evalPolyUp (c : Fin (n + 1) → 𝕋) (t : 𝕋) : 𝕋 :=
  sumUp fun i => mulRangeUp (c i) (powRange t (i : ℕ)).inf (powRange t (i : ℕ)).sup

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Taylm.Float.Operations.PolyBoundsMono

@[expose] public section

/-!
# `Taylm.boundsMono`

The range of a Taylor model, CORA's `interval` with method `'int'` as CORA.cpp computes it: the
remainder plus the range of the polynomial (`Taylm.polyBoundsMono`), then the error box, the
lower ends rounded down and the upper ones up.

## Inputs
* `T` – Taylor model

## Output
* interval holding every function the model encloses, on the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.boundsMono (T : Taylm 𝕋 n) : Interval 𝕋 :=
  let P := Taylm.polyBoundsMono T.terms
  ⟨addDown (addDown T.rem.inf P.inf) T.I_error.inf, addUp (addUp T.rem.sup P.sup) T.I_error.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

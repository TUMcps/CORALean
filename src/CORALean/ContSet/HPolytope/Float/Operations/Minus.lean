module

public import CORALean.ContSet.HPolytope.Float.Operations.Translate

@[expose] public section

/-!
# `HPolytope.minus`, over a floating-point scalar

The translation by `-v`. Negation is exact, so the subtrahend costs no rounding
of its own; the shift rounds as `translate` does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.minus (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.translate (fun i => neg (v i)) P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

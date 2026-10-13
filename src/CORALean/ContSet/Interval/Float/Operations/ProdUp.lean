module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A product rounded up

A right-nested fold of `mulUp`, which is not associative, so it names its bracketing as `sumUp`
does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def prodUp {k : ℕ} (f : Fin k → 𝕋) : 𝕋 := Fin.foldr k (fun i acc => mulUp (f i) acc) one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

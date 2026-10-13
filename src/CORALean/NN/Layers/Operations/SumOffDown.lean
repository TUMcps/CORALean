module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A sum leaving one index out, rounded down

The mirror of `sumOffUp`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑_{j ≠ i} v j`, the `i`-th term zeroed, rounded down. -/
def sumOffDown (i : Fin n) (v : Fin n → 𝕋) : 𝕋 :=
  sumDown fun j => if j = i then zero else v j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

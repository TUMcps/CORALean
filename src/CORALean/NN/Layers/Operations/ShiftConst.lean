module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# Moving a stored constant coefficient

The recentering `computeApproxError` performs, the constant coefficient moved by `s`: one
`addUp`, and the coefficient that lands is the one soundness is then measured against.

## Inputs
* `c` – stored coefficients
* `s` – shift

## Output
* coefficients with the constant moved by the shift
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constant coefficient moved by `s`, every other one left alone. -/
def shiftConst (c : Fin (m + 1) → 𝕋) (s : 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i => if i = 0 then addUp (c i) s else c i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

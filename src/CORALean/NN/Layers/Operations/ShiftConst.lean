import CORALean.Global.Float.FloatOps

/-!
# Moving a stored constant coefficient

The recentring `computeApproxError` performs, the constant coefficient moved by `s`: one
`addUp`, and the coefficient that lands is the one soundness is then measured against.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


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

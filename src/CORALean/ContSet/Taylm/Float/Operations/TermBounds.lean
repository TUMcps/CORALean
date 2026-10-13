module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Operations.Degree

@[expose] public section

/-!
# The range of one term over the box

The exact layer's three cases; `minimum`, `maximum`, `neg` and `absolute` are exact, so
nothing rounds.
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

def Taylm.termBounds (a : 𝕋 × (Fin n → ℕ)) : 𝕋 × 𝕋 :=
  if Real.Taylm.degree a.2 = 0 then (a.1, a.1)
  else if ∀ k, Even (a.2 k) then (minimum a.1 zero, maximum a.1 zero)
  else (neg (absolute a.1), absolute a.1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

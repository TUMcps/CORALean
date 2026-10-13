module

public import CORALean.ContSet.Taylm.Float.Taylm

@[expose] public section

/-!
# `Taylm.empty`

The empty model in each coordinate: no terms and the crossed remainder, lower bound `one`
and upper bound `zero`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.empty (n : ℕ) : Fin n → Taylm 𝕋 n :=
  fun _ => ⟨[], one, zero, 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

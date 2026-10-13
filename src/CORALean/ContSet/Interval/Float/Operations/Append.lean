module

public import CORALean.ContSet.Interval.Float.Interval
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `Interval.append`

Two boxes side by side: the product box, in the coordinates of one vector. Nothing rounds, the
bounds are copied.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.append (I₁ : Interval (Vec 𝕋 n₁)) (I₂ : Interval (Vec 𝕋 n₂)) :
    Interval (Vec 𝕋 (n₁ + n₂)) :=
  ⟨Fin.append I₁.inf I₂.inf, Fin.append I₁.sup I₂.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

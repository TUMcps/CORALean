import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.listMax`, over a floating-point scalar

The largest of `f` over a list, `zero` for the empty list.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.listMax {α : Type} (f : α → 𝕋) : List α → 𝕋
  | [] => zero
  | [a] => f a
  | a :: b :: l => maximum (f a) (Taylm.listMax f (b :: l))
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

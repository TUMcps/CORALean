import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.argMaxIdx`, over a floating-point scalar

The index of a largest entry, the first index when none is certified larger than the running best
by `le`.
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

def Taylm.argMaxIdx (v : List 𝕋) : ℕ :=
  (List.range v.length).foldl
    (fun best i => if le (v.getD i zero) (v.getD best zero) then best else i) 0
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

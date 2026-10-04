import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.widestCoord`, over a floating-point scalar

The coordinate of largest width `u - l` (rounded up), the last of equals; `none` for no
coordinates.
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

def Taylm.widestCoord (B : Fin n → 𝕋 × 𝕋) : Option (Fin n) :=
  (List.finRange n).foldl (fun best k => match best with
    | none => some k
    | some j =>
      if le (subUp (B j).2 (B j).1) (subUp (B k).2 (B k).1) then some k else some j) none
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

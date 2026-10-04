import CORALean.ContSet.Taylm.Float.Operations.HalveBox
import CORALean.ContSet.Taylm.Float.Operations.WidestCoord

/-!
# `Taylm.splitAt`, over a floating-point scalar

Box `i` of the list halved along its widest coordinate: the first half replaces it, the second is
appended.
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

def Taylm.splitAt (i : ℕ) (l : List (Fin n → 𝕋 × 𝕋)) : List (Fin n → 𝕋 × 𝕋) :=
  match l[i]? with
  | none => l
  | some B => match Taylm.widestCoord B with
    | none => l
    | some β => l.set i (Taylm.halveBox B β).1 ++ [(Taylm.halveBox B β).2]
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

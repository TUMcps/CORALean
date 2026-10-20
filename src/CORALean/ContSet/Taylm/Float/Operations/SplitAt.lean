module

public import CORALean.ContSet.Taylm.Float.Operations.HalveBox
public import CORALean.ContSet.Taylm.Float.Operations.WidestCoord

@[expose] public section

/-!
# `Taylm.splitAt`, over a floating-point scalar

Box `i` of the list halved along its widest coordinate: the first half replaces it, the second is
appended.

## Inputs
* `i` – box index
* `l` – list of boxes

## Output
* list with that box halved along its widest coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.splitAt (i : ℕ) (l : List (Fin n → Interval 𝕋)) : List (Fin n → Interval 𝕋) :=
  match l[i]? with
  | none => l
  | some B => match Taylm.widestCoord B with
    | none => l
    | some β => l.set i (Taylm.halveBox B β).1 ++ [(Taylm.halveBox B β).2]
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

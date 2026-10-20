module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Taylm.widestCoord`, over a floating-point scalar

The coordinate of largest width `u - l` (rounded up), the last of equals; `none` for no
coordinates.

## Inputs
* `B` – box

## Output
* index of the widest coordinate, if any
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

def Taylm.widestCoord (B : Fin n → Interval 𝕋) : Option (Fin n) :=
  (List.finRange n).foldl (fun best k => match best with
    | none => some k
    | some j =>
      if le (subUp (B j).sup (B j).inf) (subUp (B k).sup (B k).inf) then some k else some j) none
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioAt

@[expose] public section

/-!
# `Interval.boundaryRatioStep`: one step of the least ratio

Folds one coordinate's ratio bounds (or none) into the least so far: ends take `minimum` (exact).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.boundaryRatioStep (acc x : Option (𝕋 × 𝕋)) : Option (𝕋 × 𝕋) :=
  match x with
  | none => acc
  | some r => match acc with
    | none => some r
    | some a => some (minimum a.1 r.1, minimum a.2 r.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

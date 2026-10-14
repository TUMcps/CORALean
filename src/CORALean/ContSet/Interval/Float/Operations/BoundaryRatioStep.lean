module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioAt

@[expose] public section

/-!
# `Interval.boundaryRatioStep`: one step of the least ratio

Folds one coordinate's ratio bounds (or none) into the least so far: ends take `minimum` (exact).
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

def Interval.boundaryRatioStep (acc x : Option (Interval 𝕋)) : Option (Interval 𝕋) :=
  match x with
  | none => acc
  | some r => match acc with
    | none => some r
    | some a => some ⟨minimum a.inf r.inf, minimum a.sup r.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

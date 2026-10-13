import CORALean.ContSet.Taylm.Float.Operations.SplitAt
import CORALean.ContSet.Taylm.Float.Operations.ArgMaxIdx

/-!
# `Taylm.bnbStep`, over a floating-point scalar

One step of the branch and bound: the box holding the upper bound and the one holding the lower
bound are halved (lines 8-29 of the listing).
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

def Taylm.bnbStep (bnd : (Fin n → 𝕋 × 𝕋) → 𝕋 × 𝕋) (l : List (Fin n → 𝕋 × 𝕋)) :
    List (Fin n → 𝕋 × 𝕋) :=
  -- 8: the box whose interval holds the upper bound
  let αhi := Taylm.argMaxIdx (l.map fun B => (bnd B).2)
  -- 9: the box whose interval holds the lower bound
  let αlo := Taylm.argMaxIdx (l.map fun B => neg (bnd B).1)
  -- 10-16: one box holds both, and is halved; 17-29: each is halved
  if αhi = αlo then Taylm.splitAt αhi l else Taylm.splitAt αlo (Taylm.splitAt αhi l)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

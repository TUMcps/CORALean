module

public import CORALean.ContSet.Taylm.Float.Operations.SplitAt
public import CORALean.ContSet.Taylm.Float.Operations.ArgMaxIdx

@[expose] public section

/-!
# `Taylm.bnbStep`, over a floating-point scalar

One step of the branch and bound: the box holding the upper bound and the one holding the lower
bound are halved (lines 8-29 of the listing).
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

def Taylm.bnbStep (bnd : (Fin n → Interval 𝕋) → Interval 𝕋) (l : List (Fin n → Interval 𝕋)) :
    List (Fin n → Interval 𝕋) :=
  -- 8: the box whose interval holds the upper bound
  let αhi := Taylm.argMaxIdx (l.map fun B => (bnd B).sup)
  -- 9: the box whose interval holds the lower bound
  let αlo := Taylm.argMaxIdx (l.map fun B => neg (bnd B).inf)
  -- 10-16: one box holds both, and is halved; 17-29: each is halved
  if αhi = αlo then Taylm.splitAt αhi l else Taylm.splitAt αlo (Taylm.splitAt αhi l)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

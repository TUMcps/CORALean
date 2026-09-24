import CORALean.NN.Layers.Operations.BracketShift

/-!
# The radius a recentred bracket leaves

How far the stored constant actually moved, bracketed by a `subDown` and a `subUp`, each end
widening the end it can hurt: the shift is applied after the bracket was taken, so it moves the
polynomial out from under it, and this is the payment.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The radius the recentred bracket leaves, each end widened by the shift's own rounding. -/
def bracketError (c0 lo hi : 𝕋) : 𝕋 :=
  maximum (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0))
    (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

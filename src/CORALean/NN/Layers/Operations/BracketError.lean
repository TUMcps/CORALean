module

public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# The radius a recentered bracket leaves

How far the stored constant actually moved, bracketed by a `subDown` and a `subUp`, each end
widening the end it can hurt: the shift is applied after the bracket was taken, so it moves the
polynomial out from under it, and this is the payment.

## Inputs
* `c0` – stored constant
* `lo` – lower end of the bracket
* `hi` – upper end of the bracket

## Output
* radius the recentered bracket leaves
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The radius the recentered bracket leaves, each end widened by the shift's own rounding. -/
def bracketError (c0 lo hi : 𝕋) : 𝕋 :=
  maximum (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0))
    (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

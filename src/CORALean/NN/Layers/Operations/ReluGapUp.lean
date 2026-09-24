import CORALean.Global.Float.FloatOps

/-!
# ReLU's gap above a line, rounded up

How far ReLU rises above the line of slope `λ` over `[l, u]` is `max((1 - λ) u, -λ l)`; this
computes it rounding up, `(1 - λ) u` from the directed difference and `-λ l` from the negated
rounded-down product. `reluGapOfSlope_le` is that it bounds the exact gap.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The gap that slope leaves, rounded up on both ends. -/
def reluGapUp (lam l u : 𝕋) : 𝕋 :=
  maximum (subUp u (mulDown lam u)) (neg (mulDown lam l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

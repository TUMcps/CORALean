import CORALean.Global.Float.FloatOps

/-!
# The default leaky ReLU slope

CORA's `lambda = (u - α l) / (u - l)`: exact on a stable neuron — `α` below zero, `1` above — and
the secant on a crossing one. `le` is read only for a `true` answer, and any value is a legal slope
once `leakyReluRelaxation` clamps it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact on a stable neuron; the secant where the neuron crosses. -/
def leakyReluSlope (α l u : 𝕋) : 𝕋 :=
  if le u zero then α else if le zero l then one else divUp (subUp u (mulDown α l)) (subDown u l)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

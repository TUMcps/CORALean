import CORALean.Global.Float.FloatOps

/-!
# The default ReLU slope

Exact on a stable neuron — `0` below zero, `1` above — and the secant `u / (u - l)` on a crossing
one, rounded whichever way `divUp` rounds. It reads `le`, which `SoundFloatArithmetic` constrains
in no way, and does not have to: `clampUnit` makes any value a legal slope. A caller with a
better candidate passes it to `Layer.relu` instead.
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

/-- Exact on a stable neuron; the secant where the neuron crosses. -/
def reluSlope (l u : 𝕋) : 𝕋 :=
  if le u zero then zero else if le zero l then one else divUp u (subDown u l)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

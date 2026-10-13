import CORALean.NN.Layers.Operations.PolyDerivCenter
import CORALean.NN.Layers.Operations.PolyDerivRadiusUp

/-!
# The derivative bound a sampled fit asks for

What `ofSampling` asks for and nothing else supplies: an `M` with `|σ' - p'| ≤ M` on the box,
stored. The `σ'` bracket's spread around the centre through `subUp`, plus the radius, through
one `addUp`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `σ'` bracket's spread around the centre, plus the radius, rounded up. -/
def polyDerivBoundUp (c : Fin (n + 1) → 𝕋) (loD hiD l u : 𝕋) : 𝕋 :=
  addUp (maximum (subUp hiD (polyDerivCenter c)) (subUp (polyDerivCenter c) loD))
    (polyDerivRadiusUp c l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

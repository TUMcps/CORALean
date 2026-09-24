import CORALean.NN.Layers.Operations.CoarseHi
import CORALean.NN.Layers.Operations.GridChecked

/-!
# A fit's sampled bracket, upper end

And from above, branching the same way.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The checked grid's upper end where it certifies, the fallback's where it does not. -/
def fitHi (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (M dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  if gridChecked (p l u) l u (dx l u) = true then
    sampleHi (fun i => sampleDevUp E (c l u) (p l u i)) (M l u) (dx l u)
  else coarseHi E (c l u) (M l u) l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

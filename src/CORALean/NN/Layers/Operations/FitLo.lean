import CORALean.NN.Layers.Operations.CoarseLo
import CORALean.NN.Layers.Operations.GridChecked

/-!
# A fit's sampled bracket, lower end

The sampled bracket of `σ` minus the fit over one box, at the checked grid where it certifies
and the fallback where it does not: a grid that fails its checks costs precision, not soundness.
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

/-- The checked grid's lower end where it certifies, the fallback's where it does not. -/
def fitLo (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (M dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  if gridChecked (p l u) l u (dx l u) = true then
    sampleLo (fun i => sampleDevLo E (c l u) (p l u i)) (M l u) (dx l u)
  else coarseLo E (c l u) (M l u) l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

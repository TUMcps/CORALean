import CORALean.NN.Layers.Operations.SampleDevLo
import CORALean.NN.Layers.Operations.SampleLo

/-!
# The fallback bracket's lower end

The bracket a box falls back to when its grid fails its checks: one sample at the left end, the
whole width as the spacing, and no certificate needed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sample at the left end and the whole width as the spacing, from below. -/
def coarseLo (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (M l u : 𝕋) : 𝕋 :=
  sampleLo (fun _ : Fin 1 => sampleDevLo E c l) M (subUp u l)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Interval.Float.Interval
import CORALean.NN.Layers.Definitions.Relaxation

/-!
# The box a relaxation leaves each neuron

Per neuron, the deviation of `σ` from the relaxation's affine map lies in
`offset ± error` over that neuron's bounds; this is that box, widened outward — `subDown` below,
`addUp` above — which is the one place an activation layer itself rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box each neuron's deviation from its affine map is confined to, widened outward. -/
def Relaxation.box (R : Relaxation 𝕋) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => subDown (R.offset (I.inf i) (I.sup i)) (R.error (I.inf i) (I.sup i))
  sup := fun i => addUp (R.offset (I.inf i) (I.sup i)) (R.error (I.inf i) (I.sup i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

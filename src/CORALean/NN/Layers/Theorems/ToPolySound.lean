import CORALean.NN.Layers.Operations.RelaxationToPoly
import CORALean.NN.Layers.Theorems.Real.EvalPolyOne

/-!
# An affine relaxation is sound as a polynomial one

`sound` read through `evalPoly_one`: the same inequality.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.toPoly_sound {R : Relaxation 𝕋} (hR : R.Sound σ) : R.toPoly.Sound σ := by
  refine ⟨fun {l u t} hl hu => ?_⟩
  rw [Real.evalPoly_one]
  exact hR.sound hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

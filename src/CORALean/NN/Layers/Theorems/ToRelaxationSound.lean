import CORALean.NN.Layers.Operations.PolyRelaxationToRelaxation
import CORALean.NN.Layers.Theorems.Real.EvalPolyOne

/-!
# An order-1 polynomial relaxation is sound as an affine one

The same inequality, read back through `evalPoly_one`.
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

theorem PolyRelaxation.toRelaxation_sound {P : PolyRelaxation 𝕋 1} (hP : P.Sound σ) :
    P.toRelaxation.Sound σ := by
  refine ⟨fun {l u t} hl hu => ?_⟩
  have h := hP.sound hl hu
  rwa [Real.evalPoly_one] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

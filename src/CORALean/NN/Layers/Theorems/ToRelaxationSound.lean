module

public import CORALean.NN.Layers.Operations.PolyRelaxationToRelaxation
public import CORALean.NN.Layers.Theorems.Real.EvalPolyOne

@[expose] public section

/-!
# An order-1 polynomial relaxation is sound as an affine one

The same inequality, read back through `evalPoly_one`.

## Inputs
* `P` – order-one polynomial relaxation

## Hypotheses
* `hP` – relaxation is sound for the activation

## Conclusion
* the affine reading of the relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.toRelaxation_isSound {P : PolyRelaxation 𝕋 1} (hP : P.IsSound σ) :
    P.toRelaxation.IsSound σ := by
  refine ⟨fun {l u t} hl hu => ?_⟩
  have h := hP.sound hl hu
  rwa [Real.evalPoly_one] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

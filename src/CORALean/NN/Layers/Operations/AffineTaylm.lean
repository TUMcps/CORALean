module

public import CORALean.ContSet.Taylm.Float.Operations.PlusMerged
public import CORALean.ContSet.Taylm.Float.Operations.PlusScalar
public import CORALean.ContSet.Taylm.Float.Operations.Scale
public import CORALean.NN.Layers.Definitions.TaylmArray
public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# The affine layer on Taylor models, in CORA.cpp's order

CORA.cpp's `aux_affine` in `NeuralNetwork::evaluate_taylm`: output `i` is the first input model
times `W i 0`, then each further input model times its weight added in turn (`Taylm.scale`,
`Taylm.plusMerged`), and the bias added into the constant term last (`Taylm.plusScalar`). The
roundings of the coefficients go to the error boxes, zero at round to nearest.

## Inputs
* `W` – weights, `m` rows of `n + 1` (CORA.cpp starts from the first input)
* `b` – bias

## Output
* layer mapping the input models to the output models
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.affineTaylm (W : Mat 𝕋 m (n + 1)) (b : Vec 𝕋 m) :
    Layer (TaylmArray 𝕋 d) (n + 1) m where
  enclose s := ⟨fun i =>
    -- x₀ W i 0, then + x_j W i j for j = 1 .. n, then + b i
    ((List.finRange n).foldl (fun acc j => acc.plusMerged ((s.taylm j.succ).scale (W i j.succ)))
      ((s.taylm 0).scale (W i 0))).plusScalar (b i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Operations.GraphNetMaxPoolFloat
public import CORALean.NN.Theorems.GraphNetMaxPoolEval
public import CORALean.NN.Theorems.EvaluateGraphEncloses
public import CORALean.NN.Layers.Theorems.ReluRelaxationEncloses
public import CORALean.NN.Layers.Definitions.Relu

@[expose] public section

/-!
# `GraphNet.maxPool` encloses the maximum

The float MaxPool network's zonotope holds `max((D + B) x, B x)` for every `x` of the input set:
the network is the image of `Real.GraphNet.maxPool` (its weights read as reals, the ReLU's line
enclosing `relu` by `reluRelaxation_encloses`), so `GraphNet.evaluateGraph_encloses` applies, and
`Real.GraphNet.maxPool_eval` says what the exact network computes.

## Inputs
* `D` – the difference of the operands' maps
* `B` – the second operand's map
* `slots` – whether the ReLU's errors become generators
* `X` – the input set
* `x` – a point of it

## Hypotheses
* `hx` – `x` is in `X`

## Conclusion
* the maxima are in the network's zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GraphNet.maxPool_encloses (D B : Mat 𝕋 m n) (slots : Bool) (X : Zonotope (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ X.toSet) : -- --- CONCL ---
    (fun i => max (((toRealMat D + toRealMat B) *ᵥ x) i) ((toRealMat B *ᵥ x) i)) ∈
      ((GraphNet.maxPool D B slots).evaluateGraph X).toSet := by -- --- PROOF ---
  -- the float network is the exact one's image, its weights read as reals
  suffices hR : (GraphNet.maxPool D B slots).Images
      (Real.GraphNet.maxPool (toRealMat D) (toRealMat B)) by
    have := GraphNet.evaluateGraph_encloses hR X hx
    rwa [Real.GraphNet.maxPool_eval] at this
  have h : (GraphNet.maxPool D B slots).Images _ :=
    .layer (.elementwise slots (reluRelaxation_encloses reluSlope)) (.layer .identity .done)
  convert h using 1
  -- the zero biases and the identity, read as reals
  simp only [Real.GraphNet.maxPool, GraphLayer.toReal, Real.GraphNet.layer.injEq,
    Real.GraphLayer.mk.injEq, List.map_cons, List.map_nil, true_and, and_true, heq_eq_eq]
  and_intros
  all_goals first
    | (funext i j; rw [toRealMat, toReal_diagonalBlock]
       simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply])
    | (funext i; simp [toRealVec, toReal_zero])
    | rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

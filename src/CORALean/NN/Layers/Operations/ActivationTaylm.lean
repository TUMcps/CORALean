import CORALean.ContSet.Conversion.Float.Taylm_to_Interval
import CORALean.ContSet.Taylm.Float.Operations.Const
import CORALean.ContSet.Taylm.Float.Operations.Plus
import CORALean.ContSet.Taylm.Float.Operations.Pow
import CORALean.ContSet.Taylm.Float.Operations.Smul
import CORALean.ContSet.Taylm.Float.Operations.Sum
import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Definitions.TaylmArray
import CORALean.NN.Layers.Layer

/-!
# The activation layer on Taylor models

CORA's `nnActivationLayer/evaluateTaylm` and its `evaluateTaylmNeuron`: per neuron, the
range `[l, u]` of the input model, the polynomial fit and its error `d` on that range, and then
`r = c₀ + [-d, d] + Σ_{k ≥ 1} c_k · input^k`, the powers taken by the Taylor model's own `pow`
and the coefficients applied as exact factors. CORA stores the fit highest degree first;
`PolyRelaxation.coeffs` is lowest first, so `c₀` is CORA's `coeffs(end)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n deg d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One fit per neuron, on the range of that neuron's input model. -/
def Layer.activationTaylm (P : LayerRelaxation 𝕋 n deg) :
    Layer (TaylmArray 𝕋 d) n n where
  enclose s :=
    let bounds := Taylm.interval s.taylm
    ⟨fun i =>
      let input := s.taylm i
      let l := bounds.inf i
      let u := bounds.sup i
      let coeffs := (P i).coeffs l u
      let err := (P i).error l u
      let r := (Taylm.const d (coeffs 0) input.maxOrder).plus
        ⟨[], neg err, err, input.maxOrder⟩
      r.plus (Taylm.sum fun k : Fin deg =>
        (input.pow ((k : ℕ) + 1)).smul (coeffs k.succ) (coeffs k.succ))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

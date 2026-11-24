module

public import CORALean.ContSet.Taylm.Float.Operations.BoundsMono
public import CORALean.ContSet.Taylm.Float.Operations.FromRange
public import CORALean.ContSet.Taylm.Float.Operations.PlusMerged
public import CORALean.ContSet.Taylm.Float.Operations.PowBinary
public import CORALean.ContSet.Taylm.Float.Operations.Scale
public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Definitions.TaylmArray
public import CORALean.NN.Layers.Layer
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The activation layer on Taylor models, in CORA.cpp's order

CORA.cpp's `aux_neuron` in `NeuralNetwork::evaluate_taylm`, per neuron: the bounds `[l, u]` of the
input model `x` (`Taylm.boundsMono`, CORA.cpp's `bounds`), the fit `c` and its error `d` on that
range, then `r = constant(c₀) + fromRange(-d, d)` and `r += x^k · c_k` for `k = 1, …, top`, the
powers by binary exponentiation (`Taylm.powBinary`, CORA.cpp's `power`) and each scaled by its
coefficient (`Taylm.scale`). `top l u ≤ deg` is the degree of the fit on the box: CORA.cpp's
polynomial has fewer coefficients where the activation is linear, and the powers above it are not
added. The coefficients are lowest first: `c₀` is CORA.cpp's `coeffs.back()`.

## Inputs
* `P` – the fit of every neuron
* `top` – the degree of every neuron's fit on a box

## Output
* layer fitting each neuron on the range of its input model
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n deg d : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- One neuron: `c₀ + [-e, e]`, then the powers of `x` up to `top`, each times its coefficient. -/
@[step_of Layer.activationTaylmFit]
def step_activationTaylmNeuron (P : PolyRelaxation 𝕋 deg) (top : 𝕋 → 𝕋 → ℕ)
    (x : Taylm 𝕋 d) : Taylm 𝕋 d :=
  let B := x.boundsMono
  let c := P.coeffs B.inf B.sup
  let e := P.error B.inf B.sup
  let r := (Taylm.constSparse d (c 0) x.maxOrder).plusMerged
    (Taylm.fromRange d (neg e) e x.maxOrder)
  (List.finRange deg).foldl (fun r (k : Fin deg) =>
    if (k : ℕ) < top B.inf B.sup then r.plusMerged ((x.powBinary ((k : ℕ) + 1)).scale (c k.succ))
    else r) r


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.activationTaylmFit (P : LayerRelaxation 𝕋 n deg) (top : Fin n → 𝕋 → 𝕋 → ℕ) :
    Layer (TaylmArray 𝕋 d) n n where
  enclose s := ⟨fun i => step_activationTaylmNeuron (P i) (top i) (s.taylm i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

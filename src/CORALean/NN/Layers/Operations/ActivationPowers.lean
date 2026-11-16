module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGens
public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPowers
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.LayerRelaxationBox
public import CORALean.NN.Layers.Operations.PolyBoxIndep

@[expose] public section

/-!
# The activation layer at a polynomial relaxation, by the powers of the set

CORA's `evaluatePolyZonotope` of an activation layer at order `k`, as CORA.cpp's
`priv_layer_poly` computes it when no generator limit is set: each neuron's fit on its row by the
powers of the row (`PolyZonotope.evalPowers`, which keeps the independent generators), the
generators of equal exponents added (`compactGens`, the factors kept), then the error of the fit
as independent generators (`add_approx_error_to_GI`). The fit is the relaxation's: CORA's fits
(regression, Bernstein, Taylor) are not formalized, so the coefficients and the error are data,
and the theorem assumes they are sound (`PolyRelaxation.Encloses`). `Layer.activationPoly` is the
same layer by Horner's rule.

## Inputs
* `P` – polynomial relaxation of every neuron

## Output
* layer applying the fits by the powers of the set and adding their errors as generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.activationPowers (P : LayerRelaxation 𝕋 n m) : Layer 𝒫𝒵[𝕋] n n where
  enclose s := Plus.plus (s.evalPowers (P.coeffList s.interval)).compactGens
    (OfInterval.polyIndep.ofInterval (P.box s.interval))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

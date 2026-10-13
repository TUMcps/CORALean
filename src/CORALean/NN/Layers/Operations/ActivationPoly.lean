module

public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.LayerRelaxationBox
public import CORALean.NN.Layers.Operations.LayerRelaxationCoeffList

@[expose] public section

/-!
# The activation layer at a polynomial relaxation

CORA's `evaluatePolyZonotopeNeuron` [1]: a fit per neuron at its order in the pattern
[1, Eq. 23], at the common degree padding brings them to, evaluated through
`PolyZonotope.evalPoly` with only what the fits miss thrown into a box.
`Layer.activation` keeps a slope and boxes the rest; this keeps a degree-`m` dependence, which is
the precision refinement spends. Pinned to the polynomial zonotope, no other representation
being closed under `evalPoly`; `dependent` runs first, so the input's independent generators
become dependent ones and the cross terms [2, Prop. 2] spends a factor on are kept. The box is
centred at zero, so the layer rounds nowhere of its own.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
* [2] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `dependent` first, then each neuron's fit on the set, then the residual box. -/
def Layer.activationPoly (P : LayerRelaxation 𝕋 n m) :
    Layer (fun k => Float.PolyZonotope (Vec 𝕋 k)) n n where
  enclose s := Plus.plus (s.dependent.evalPoly (P.coeffList s.interval))
    (Interval.polyZonotope (P.box s.interval))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.LayerRelaxationBox
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# The polynomial activation layer over the exact polynomial zonotope

The activation layer at a polynomial relaxation [1], at the exact polynomial zonotope, where
`evalPoly` and `plus` are exact: a fit per neuron evaluated through `PolyZonotope.evalPoly` and only
what the fits miss thrown into a box. [2, Alg. 1] is this at `m = 2`. `activationPolyOn` fits the
neurons on a box handed to it rather than the input's own — [1, Prop. 4.2].

ℝ-only, the representation being the exact one: the runnable layer is `Layer.activationPoly` at the
stored polynomial zonotope, which rounds.

## Inputs
* `P` – polynomial relaxation of the activation

## Output
* layer applying the fits neuron by neuron and boxing the residual

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
* [2] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `dependent` first, then each neuron's fit on the set, then the residual box. -/
noncomputable def Layer.activationPoly (P : LayerRelaxation ℝ n m) : Layer 𝒫𝒵 n n where
  enclose s :=
    plus (s.dependent.evalPoly (P.coeffList
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))))
      (Interval.polyZonotope (P.box
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).nominal)

/-- The activation layer at a box `J` handed to it: every fit and the residual box read `J`. -/
noncomputable def Layer.activationPolyOn (P : LayerRelaxation ℝ n m)
    (J : Interval (Vec ℝ n)) : Layer 𝒫𝒵 n n where
  enclose s := plus (s.dependent.evalPoly (P.coeffList (⟨J.inf, J.sup⟩ : Float.Interval (Vec ℝ n))))
    (Interval.polyZonotope (P.box (⟨J.inf, J.sup⟩ : Float.Interval (Vec ℝ n))).nominal)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

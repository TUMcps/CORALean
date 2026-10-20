module

public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.DependentP
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.EvalPolyH
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.PlusP
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# The exact polynomial activation layer's generator count

ℝ-only, as the layer is. [1, Lemma 4.3]: a closed form in the input's own `s.h + s.q` and the
layer's shared degree `m` — `Alg. 1` line 9's padding — with nothing of the fits beyond `m`
reaching it, and `n` more from the residual box.

## Inputs
* `P` – relaxation of every neuron
* `s` – input polynomial zonotope

## Hypotheses
* none

## Conclusion
* the output has the stated number of dependent generators

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPoly_enclose_h (P : LayerRelaxation ℝ n m)
    (s : PolyZonotope (Vec ℝ n)) : -- --- CONCL ---
    ((Layer.activationPoly P).enclose s).h = (s.h + s.q + 1) *
      (∑ i ∈ Finset.range (m + 1), (s.h + s.q + 1) ^ i) + n := by -- --- PROOF ---
  show (PolyZonotope.plus
      (s.dependent.evalPoly (P.coeffList
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))))
      (Interval.polyZonotope (P.box
        (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).nominal)).h = _
  have hlen :
      (P.coeffList (⟨s.interval.inf, s.interval.sup⟩ : Float.Interval (Vec ℝ n))).length = m + 1 :=
    List.length_ofFn
  rw [PolyZonotope.plus_h, PolyZonotope.evalPoly_h, PolyZonotope.dependent_h, hlen,
    Interval.polyZonotope_h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

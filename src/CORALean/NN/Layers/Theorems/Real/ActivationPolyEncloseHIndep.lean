module

public import CORALean.NN.Layers.Theorems.Real.ActivationPolyEncloseH

@[expose] public section

/-!
# The generator count ignores the fits

ℝ-only, as the layer is. [1, Lemma 4.3] in words: same order pattern on the same input, same
generator count, whatever the individual neurons' own fits.

## Inputs
* `P` – relaxation of every neuron
* `P'` – second relaxation of every neuron
* `s` – input polynomial zonotope

## Hypotheses
* none

## Conclusion
* the generator count does not depend on the fits

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

theorem Layer.activationPoly_enclose_h_indep (P P' : LayerRelaxation ℝ n m)
    (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).h = ((Layer.activationPoly P').enclose s).h := by
  rw [Layer.activationPoly_enclose_h, Layer.activationPoly_enclose_h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

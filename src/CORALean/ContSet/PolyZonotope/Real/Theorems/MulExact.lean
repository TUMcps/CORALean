module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact

@[expose] public section

/-!
# `mul` is exactly the product over shared factors

At one dimension this is [1, Prop. 2.9]; `bilin_exact` at the entrywise product is what `mul`
is. `construct (mul pZ₁ pZ₂)` is not `construct pZ₁ * construct pZ₂`: both sets are functions
of one shared factor vector, so their pointwise product ranges over far fewer points than the
product of the two sets. The claim is about the evaluation map: the result is exactly the
image of the admissible factors under `a ↦ point pZ₁ a ⊙ point pZ₂ a`, with `pZ₂` read at the
same factors through `Fin.cast`. `point` ignores the independent blocks, so they take no part.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the product over shared factors equals the result

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   21-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mul_exact (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (fun a : Fin pZ₁.p → ℝ => pZ₁.point a * pZ₂.point (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (pZ₁.mul pZ₂ hp).construct :=
  PolyZonotope.bilin_exact Entrywise.hadamardLin pZ₁ pZ₂ hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

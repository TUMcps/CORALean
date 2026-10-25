module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# `PolyZonotope.exactCartProd`

[1, Prop. 2.12]: the pair of two sets written over *one* factor list. Each operand is embedded
into the product at zero in the other coordinate and the two are added with `exactPlus`, so
the exponent matrices lie side by side rather than block-diagonally, the whole difference from
`cartProd`. It is not the Cartesian product: both coordinates are functions of the same factor
vector, so the claim is `exactCartProd_point`, about the pairing map. [1] additionally shares
the first `q₁` independent generators; here they stay separate, so this result contains [1]'s.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* Cartesian product sharing the factors

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pair of two sets over one shared factor list. -/
def PolyZonotope.exactCartProd (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (α × β) :=
  (pZ₁.map (LinearMap.inl ℝ α β)).exactPlus (pZ₂.map (LinearMap.inr ℝ α β)) hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import Mathlib.LinearAlgebra.Prod

/-!
# `PolyZonotope.exactCartProd`

[1, Prop. 2.12]: the pair of two sets written over *one* factor list. Each
operand is embedded into the product at zero in the other coordinate and the
two are added with `exactPlus`, so the exponent matrices lie side by side
rather than block-diagonally — the whole difference from `cartProd`.

What it denotes is not the Cartesian product, and cannot be: both coordinates
are functions of the same factor vector, so the claim is `exactCartProd_point`,
about the pairing map, exactly as `exactPlus_point` is for the sum.

[1] additionally shares the first `q₁` *independent* generators, its `PZ₂`
being written as `⟨c₂, [G₂ Ĝ₂], [G_{I,2} Ĝ_{I,2}], [E₁ E₂]⟩`. Here they stay
separate, as `exactPlus` keeps them, so this result contains [1]'s; the
per-neuron sets [1, Alg. 1] pairs have no independent block at all.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


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

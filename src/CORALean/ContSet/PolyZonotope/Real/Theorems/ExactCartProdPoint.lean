module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactCartProd
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint

@[expose] public section

/-!
# `exactCartProd` pairs the two points

What [1, Prop. 2.12] calls a Cartesian product, and what it cannot mean: both
coordinates are read off one factor vector, so the result is a subset of
`construct pZ₁ ×ˢ construct pZ₂` and generally a proper one — `cartProd` is
what computes the product itself.

The two embeddings are linear, so `map_point` carries each operand's point into
its own coordinate and `exactPlus_point` adds them; `pZ₂` is read at `pZ₁`'s
factor indices through `Fin.cast`, as it is there.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the pair of the two points

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.exactCartProd_point (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) :
    (pZ₁.exactCartProd pZ₂ hp).point a
      = (pZ₁.point a, pZ₂.point fun k => a (Fin.cast hp.symm k)) := by -- --- PROOF ---
  show ((pZ₁.map (LinearMap.inl ℝ α β)).exactPlus
    (pZ₂.map (LinearMap.inr ℝ α β)) hp).point a = _
  -- the sum of the two embedded points, each moved by its own embedding
  rw [PolyZonotope.exactPlus_point, PolyZonotope.map_point, PolyZonotope.map_point]
  simp only [LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  -- the two `Fin.cast` proofs differ as terms and not as functions
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

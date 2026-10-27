module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `ZonoBundle.plus`

CORA's `zonoBundle`/`plus` [1, Prop. 2]: every pair of zonotopes, one from each bundle,
summed and indexed through `finProdFinEquiv`. An *enclosure*, never exact — a
sum of intersections is not an intersection of sums, and nothing here records
that the same point of each intersection was the one summed in every pair.

## Inputs
* `zB₁` – first summand
* `zB₂` – second summand

## Output
* enclosure of the Minkowski sum

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.plus (zB₁ zB₂ : ZonoBundle α) : ZonoBundle α where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    Zonotope.plus (zB₁.Z (finProdFinEquiv.symm p).1) (zB₂.Z (finProdFinEquiv.symm p).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

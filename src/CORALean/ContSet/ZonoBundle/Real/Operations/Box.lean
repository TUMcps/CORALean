module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `ZonoBundle.box`: the enclosing box of a bundle

The smallest box containing the bundle's intersection, `box(Z_∩)` of [1, Prop. 6]: the
intersection of every interval that contains it. Nothing is computed — this is the
tight box the proposition bounds, not an algorithm for it.

## Inputs
* `zB` – zonotope bundle

## Output
* the smallest box containing the bundle

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.box (zB : ZonoBundle α) : Set α :=
  ⋂ I : {I : Interval α // zB.construct ⊆ I.construct}, I.1.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

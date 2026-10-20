module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.Box
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The bundle's box lies in every member's box

[1, Prop. 6]: `box(Z_∩) ⊆ {box(Z₁), …, box(Z_s)}_∩`. Each member contains the
intersection, so the member's box `Zonotope.interval` is one of the intervals that
`ZonoBundle.box` intersects. The paper skips the proof as obvious.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* none

## Conclusion
* its box lies in every member's box

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.box_subset_interval (zB : ZonoBundle α) : -- --- CONCL ---
    zB.box ⊆ ⋂ i, (zB.Z i).interval.construct := by -- --- PROOF ---
  refine Set.subset_iInter fun i => ?_
  refine Set.iInter_subset_of_subset
    ⟨(zB.Z i).interval,
      (SetIntersection.construct_subset_ofFn _ i).trans (Zonotope.interval_contains _)⟩ ?_
  exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

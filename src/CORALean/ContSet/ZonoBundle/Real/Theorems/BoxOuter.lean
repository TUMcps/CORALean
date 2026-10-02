import CORALean.ContSet.ZonoBundle.Real.Operations.Box
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import Mathlib.Order.BourbakiWitt

/-!
# The bundle's box lies in every member's box

[1, Prop. 6]: `box(Z_∩) ⊆ {box(Z₁), …, box(Z_s)}_∩`. Each member contains the
intersection, so the member's box `Zonotope.interval` is one of the intervals that
`ZonoBundle.box` intersects. The paper skips the proof as obvious.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.box_subset_interval (zB : ZonoBundle α) :
    zB.box ⊆ ⋂ i, (zB.Z i).interval.construct := by
  refine Set.subset_iInter fun i => ?_
  refine Set.iInter_subset_of_subset
    ⟨(zB.Z i).interval, (Set.iInter_subset _ i).trans (Zonotope.interval_contains _)⟩ ?_
  exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

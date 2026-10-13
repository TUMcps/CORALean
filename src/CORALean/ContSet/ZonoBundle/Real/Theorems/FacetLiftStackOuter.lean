import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStack

/-!
# Props. 3 and 4 combined

`⋂ᵢ (Zᵢ ⊕ Z_add) ⊆ Z_∩ ↑ Z_add` [1, Prop. 3], the chain the paper writes after
Prop. 4, for members given as halfspaces: Prop. 3 member by member, then Prop. 4 to read
the right side as the lift of the bundle.

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

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.facetLift_stack_outer (P : Fin s → HPolytope α) (Zadd : Zonotope α) :
    ⋂ i, ((P i).construct + Zadd.construct) ⊆
      ((HPolytope.stack P).facetLift Zadd).construct := by
  rw [HPolytope.facetLift_stack_exact]
  exact Set.iInter_mono fun i => HPolytope.facetLift_outer (P i) Zadd

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

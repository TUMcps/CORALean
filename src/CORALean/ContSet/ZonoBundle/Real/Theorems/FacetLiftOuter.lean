import CORALean.ContSet.ZonoBundle.Real.Operations.FacetLift

/-!
# Facet lifting encloses the Minkowski sum

[1, Prop. 3]: `Z ⊕ Z_add ⊆ Z ↑ Z_add`. A sum point `x + y` has `eᵢ (x + y) ≤ dᵢ +
eᵢ y ≤ dᵢ + max(eᵢ Z_add)`.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.facetLift_outer (P : HPolytope α) (Zadd : Zonotope α) :
    P.construct + Zadd.construct ⊆ (P.facetLift Zadd).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  refine ⟨fun i => ?_, fun i => i.elim0⟩
  rw [map_add]
  exact add_le_add (hx.1 i) ((Zadd.supportBound (P.A i)).le y hy)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

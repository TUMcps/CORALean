module

public import CORALean.ContSet.ZonoBundle.Real.Operations.FacetLift
public import CORALean.ContSet.HPolytope.Real.Theorems.StackExact

@[expose] public section

/-!
# Lifting the facets of a bundle is lifting each member's

[1, Prop. 4]: the H-representation of a bundle stacks the members' rows, and a lifted
row depends on its own row alone, so lifting the stack and stacking the lifted members
are the same constraint list read in two groupings. `facetLift_stack_exact` is
the equation; `FacetLiftStackOuter` combines it with Prop. 3.

## Inputs
* `P` – family of polytopes
* `Zadd` – zonotope added

## Hypotheses
* none

## Conclusion
* lifting the stacked facets is lifting each polytope's facets

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
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

theorem HPolytope.facetLift_stack_exact (P : Fin s → HPolytope α)
    (Zadd : Zonotope α) : -- --- CONCL ---
    ((HPolytope.stack P).facetLift Zadd).construct =
      ⋂ i, ((P i).facetLift Zadd).construct := by -- --- PROOF ---
  ext x
  simp only [HPolytope.construct, HPolytope.facetLift, HPolytope.stack, Set.mem_iInter,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, -⟩ i
    refine ⟨fun j => ?_, fun j => j.elim0⟩
    have := h1 (finSigmaFinEquiv ⟨i, j⟩)
    rwa [Equiv.symm_apply_apply] at this
  · intro h
    exact ⟨fun r => (h _).1 _, fun r => r.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

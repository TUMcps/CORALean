module

public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# [1, Thm. 2]'s normal at a selection that repeats a generator

A selection that names the same generator twice has a cross product with two equal columns, so it
is `0`, and its row of [1, Thm. 2] holds trivially. This is what leaves only the injective
selections, the generator subsets, for the `Bool × Finset` indexing.

## Inputs
* `n` – dimension minus one
* `Z` – zonotope
* `S` – selected generator indices

## Hypotheses
* `hS` – selection has a repeat

## Conclusion
* the facet normal is zero

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A selection with a repeated generator has cross product `0`. -/
theorem Zonotope.facetNormal_eq_zero_of_not_injective {n : ℕ} (Z : Zonotope (Vec ℝ (n + 1)))
    (S : Fin n → Fin Z.h) (hS : ¬Function.Injective S) : -- --- CONCL ---
    Z.facetNormal S = 0 := by -- --- PROOF ---
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hS
  refine dotProduct_eq_zero _ fun y => ?_
  unfold Zonotope.facetNormal
  rw [dotProduct_comm, dotProduct_nCross]
  exact Matrix.det_zero_of_column_eq (i := a.succ) (j := b.succ)
    (fun h => hne (Fin.succ_injective _ h)) fun k => by simp [hab]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

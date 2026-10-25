module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A zonotope as halfspaces

`Zonotope.supportBound` answers a direction without a linear program, exactly, at one dot product
per generator, which is where the two representations meet. The rows are the caller's. Exact when
they are the zonotope's own facet normals, of which there are `2·C(h, n-1)`, the reason CORA does
not convert a zonotope to halfspaces unless it has to. `supportBound` is the `d̃` of [1, Prop. 4],
where a halfspace description absorbs a zonotope without enumerating either one's vertices.

## Inputs
* `Z` – zonotope
* `Aq` – direction functionals

## Hypotheses
* none

## Conclusion
* zonotope is contained in its halfspace polytope

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hPolytope_contains (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    Z.construct ⊆ (Z.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

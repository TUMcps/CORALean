import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds

/-!
# Vertices to halfspaces

The cheap direction. Checking a vertex against a row is arithmetic, and if every
vertex passes then so does every combination of them, so a row's bound is just
the furthest vertex along it.

Which rows is the caller's choice, and that is the whole of the imprecision:
exact when the directions contain the hull's facet normals, which is what a
convex-hull implementation produces. Enumerating them is a precision question
rather than a soundness one, so it stays outside — hand this qhull's normals and
the result is CORA's `constraints`, with a certificate that costs one check per
vertex per row.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

noncomputable def VPolytope.hPolytope (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  HPolytope.ofBounds Aq fun i => P.supportBound (Aq i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.hPolytope_contains (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    P.construct ⊆ (P.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

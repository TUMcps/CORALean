import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# Vertices to halfspaces

The cheap direction of the conversion. Checking a vertex against a row is
arithmetic, and if every vertex passes then so does every combination of them,
so a row's bound is just the furthest vertex along it.

Which rows is the caller's choice. Exact when the directions contain the hull's
facet normals — enumerating those is the expensive part, and it is a precision
question rather than a soundness one, so it stays outside.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

noncomputable def VPolytope.toH (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => P.supportBound (Aq i)

theorem VPolytope.subset_toH (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    P.construct ⊆ (P.toH Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real

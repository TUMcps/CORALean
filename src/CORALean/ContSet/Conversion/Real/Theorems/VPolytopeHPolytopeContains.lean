module

public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# Vertices to halfspaces

The cheap direction. Checking a vertex against a row is arithmetic, and if every vertex passes then
so does every combination of them, so a row's bound is the furthest vertex along it. Which rows is
the caller's choice, and that is the whole of the imprecision: exact when the directions contain the
hull's facet normals, which a convex-hull implementation produces. Enumerating them is a precision
question rather than a soundness one, so it stays outside: hand this qhull's normals and the result
is CORA's `constraints`, with a certificate costing one check per vertex per row.

## Inputs
* `P` – vertex polytope
* `Aq` – direction functionals

## Hypotheses
* none

## Conclusion
* polytope is contained in its halfspace polytope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.hPolytope_contains (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    P.construct ⊆ (P.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

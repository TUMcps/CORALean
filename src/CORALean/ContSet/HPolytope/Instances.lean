import CORALean.ContSet.HPolytope.HPolytope

/-!
# What `HPolytope` instantiates

`ContSet` and no more: a halfspace description computes none of `plus`,
`linComb` or `reduce` without enumerating vertices first, so it instantiates
none of them and owes nothing. `and` and `comap` stay named operations, which is
what a constrained zonotope's coefficient domain is built from.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (HPolytope α) α :=
  ⟨HPolytope.construct⟩

end CORALean.Real

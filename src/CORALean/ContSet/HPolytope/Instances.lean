import CORALean.ContSet.HPolytope.Theorems.API

/-!
# What `HPolytope` instantiates

`ContSet` and no more. `OuterContSet` asks for `plus`, `linComb` and `reduce`,
none of which a halfspace description computes without enumerating vertices
first. `and` and `comap` stay named operations, which is what a constrained
zonotope's coefficient domain is built from.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (HPolytope α) α :=
  ⟨HPolytope.construct⟩

end CORALean.Real

import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.point`

One vertex, which is the singleton. Composed with `plus` this is a translation,
so the representation needs no separate one.

One vertex, which is the singleton.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def VPolytope.point (v : α) : VPolytope α := ⟨1, fun _ => v⟩

end CORALean.Real

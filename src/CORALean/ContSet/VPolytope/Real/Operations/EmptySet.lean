import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.emptySet`

No vertices: there is no coefficient family over an empty index summing to one,
so this denotes `∅`. A vertex description needs no unsatisfiable row to say it,
unlike a halfspace one.

What `intersection` returns when two polytopes are shown disjoint.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.emptySet (α : Type) : VPolytope α := ⟨0, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

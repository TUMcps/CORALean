import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.emptySet`

No vertices: there is no coefficient family over an empty index summing to one,
so this denotes `∅`. A vertex description needs no unsatisfiable row to say it,
unlike a halfspace one.

What `and` returns when two polytopes are shown disjoint.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def VPolytope.emptySet (α : Type) : VPolytope α := ⟨0, Fin.elim0⟩

theorem VPolytope.construct_emptySet : (VPolytope.emptySet α).construct = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, hsum, -⟩
  -- ascribed at the projection spelling of the count, which is `0` only by defeq
  have hz : ∑ j : Fin (VPolytope.emptySet α).k, β j = 0 := Fin.sum_univ_zero _
  rw [hz] at hsum
  linarith

end CORALean.Real

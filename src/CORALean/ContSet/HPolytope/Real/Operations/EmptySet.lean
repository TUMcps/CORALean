import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.emptySet`

One unsatisfiable row, `0 ≤ -1`: the absorbing element of `and`, and what a
halfspace description says when it has nothing.

Stated with a row rather than with no points at all, because a representation
has to denote `∅` by data a machine can hold.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def HPolytope.emptySet (α : Type) [AddCommGroup α] [Module ℝ α] : HPolytope α where
  m := 1
  A := fun _ => 0
  b := fun _ => -1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

theorem HPolytope.construct_emptySet : (HPolytope.emptySet α).construct = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hle, -⟩
  -- the row index ascribed at `Fin 1`, the count's reduced spelling
  have h : (0:ℝ) ≤ -1 := hle (0 : Fin 1)
  linarith

end CORALean.Real

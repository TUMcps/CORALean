import CORALean.ContSet.Interval.Real.Interval

/-!
# `IsNonempty` is nonemptiness

`inf` is the witness one way, transitivity through any point the other. Negated,
it is the claim that crossed bounds denote `∅`.

The predicate itself is stated here rather than beside the structure: it is one
line, nothing but this file gives it a meaning, and every use of it is a use of
the equivalence below.
-/

-- Authors:       Tobias Ladner
-- Written:       17-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Bounds that do not cross, coordinate by coordinate. -/
def Interval.IsNonempty (I : Interval α) : Prop := ∀ i : ι, entry I.inf i ≤ entry I.sup i

theorem Interval.isNonempty_iff (I : Interval α) : I.IsNonempty ↔ I.construct.Nonempty := by
  constructor
  · exact fun h => ⟨I.inf, fun i => ⟨le_refl _, h i⟩⟩
  · rintro ⟨x, hx⟩ i
    exact le_trans (hx i).1 (hx i).2

theorem Interval.not_isNonempty_iff (I : Interval α) : ¬I.IsNonempty ↔ I.construct = ∅ := by
  rw [Interval.isNonempty_iff, Set.not_nonempty_iff_eq_empty]

end CORALean.Real

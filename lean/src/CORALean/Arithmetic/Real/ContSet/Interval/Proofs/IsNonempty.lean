import CORALean.Arithmetic.Real.ContSet.Interval.API

/-!
# `IsNonempty` is nonemptiness

`inf` is the witness one way, transitivity through any point the other. Negated,
it is `API`'s claim that crossed bounds denote `∅`.
-/

-- Authors:       Tobias Ladner
-- Written:       17-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Interval.Proofs

variable {n : ℕ}

theorem isNonempty_iff (I : Interval n) : I.IsNonempty ↔ I.construct.Nonempty := by
  constructor
  · exact fun h => ⟨I.inf, fun i => ⟨le_refl (I.inf i), h i⟩⟩
  · rintro ⟨x, hx⟩ i
    exact le_trans (hx i).1 (hx i).2

theorem not_isNonempty_iff (I : Interval n) : ¬I.IsNonempty ↔ I.construct = ∅ := by
  rw [isNonempty_iff, Set.not_nonempty_iff_eq_empty]

end CORALean.Arithmetic.Real.Interval.Proofs

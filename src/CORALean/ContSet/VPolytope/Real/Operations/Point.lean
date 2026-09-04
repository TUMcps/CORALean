import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.point`

One vertex, which is the singleton. Composed with `plus` this is a translation,
so the representation needs no separate one.

The set it denotes takes both directions of an `ext`, each of them working at
`Fin 1` — the count's reduced spelling, which is what `Fin.sum_univ_one`
matches against.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def VPolytope.point (v : α) : VPolytope α := ⟨1, fun _ => v⟩

theorem VPolytope.construct_point (v : α) : (VPolytope.point v).construct = {v} := by
  ext x
  constructor
  · rintro ⟨β, -, hsum, rfl⟩
    refine Set.mem_singleton_iff.mpr ?_
    -- shown at `Fin 1`, the count's reduced spelling, so `Fin.sum_univ_one` matches
    have h1 : β (0 : Fin 1) = 1 := by
      rw [← hsum]
      exact (Fin.sum_univ_one (β : Fin 1 → ℝ)).symm
    show ∑ j : Fin 1, β j • v = v
    rw [Fin.sum_univ_one, h1, one_smul]
  · rintro rfl
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, ?_⟩
    · show ∑ _j : Fin 1, (1:ℝ) = 1
      rw [Fin.sum_univ_one]
    · show x = ∑ _j : Fin 1, (1:ℝ) • x
      rw [Fin.sum_univ_one, one_smul]

end CORALean.Real

module

public import CORALean.ContSet.VPolytope.Real.Operations.Point

@[expose] public section

/-!
# `VPolytope.point` denotes the singleton

The set it denotes takes both directions of an `ext`, each of them working at
`Fin 1` — the count's reduced spelling, which is what `Fin.sum_univ_one`
matches against.

## Inputs
* `v` – point

## Hypotheses
* none

## Conclusion
* the one-vertex polytope denotes `{v}`
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_point (v : α) : -- --- CONCL ---
    (VPolytope.point v).construct = {v} := by -- --- PROOF ---
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

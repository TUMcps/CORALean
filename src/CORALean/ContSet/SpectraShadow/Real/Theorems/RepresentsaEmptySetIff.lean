module

public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `SpectraShadow.representsa_emptySet` is emptiness

The inequality has no solution exactly when the set is `∅`.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `representsa_emptySet` holds iff the shadow is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_emptySet_iff (S : SpectraShadow α) : -- --- CONCL ---
    S.representsa_emptySet ↔ S.construct = ∅ := by -- --- PROOF ---
  unfold SpectraShadow.representsa_emptySet
  constructor
  · -- a point would give a solution
    intro h
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨β, hβ, -⟩
    exact h ⟨β, hβ⟩
  · -- a solution gives a point
    rintro h ⟨β, hβ⟩
    have : (S.c + ∑ i, β i • S.G i) ∈ S.construct := ⟨β, hβ, rfl⟩
    rw [h] at this
    exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

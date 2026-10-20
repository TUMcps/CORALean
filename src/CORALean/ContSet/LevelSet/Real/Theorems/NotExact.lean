module

public import CORALean.ContSet.LevelSet.Real.Operations.Not

@[expose] public section

/-!
# `LevelSet.not` is the complement

Where CORA's `not` is defined, the result denotes exactly the complement.

## Inputs
* `L` – single-constraint level set

## Hypotheses
* none

## Conclusion
* every result is the complement of `L`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.not_exact {L : LevelSet n} : -- --- CONCL ---
    ∀ L' ∈ L.not,
      L'.construct = L.construct ᶜ := by -- --- PROOF ---
  intro L' (h : L.not = some L')
  obtain ⟨m, f, op⟩ := L
  match m, f, op, h with
  | 1, f, op, h =>
    simp only [LevelSet.not] at h
    revert h
    cases hop : op 0 <;> simp only [reduceCtorEq, Option.some.injEq]
    · rintro rfl
      ext x
      simp [LevelSet.construct, Fin.forall_fin_one, hop, CompOp.holds]
    · rintro rfl
      ext x
      simp [LevelSet.construct, Fin.forall_fin_one, hop, CompOp.holds]
    · intro h
      exact h.elim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
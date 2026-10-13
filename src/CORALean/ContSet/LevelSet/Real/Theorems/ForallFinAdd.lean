module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# Quantifying over a stacked index

A statement about every index of `Fin (a + b)` splits into the first `a` and the last `b`. What
the stacked constraints of `and_` and the two-sided bounds of `Interval.levelSet` need.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.forall_fin_add {a b : ℕ} (P : Fin (a + b) → Prop) :
    (∀ i, P i) ↔ (∀ i : Fin a, P (Fin.castAdd b i)) ∧ ∀ j : Fin b, P (Fin.natAdd a j) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun h i => Fin.addCases h.1 h.2 i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

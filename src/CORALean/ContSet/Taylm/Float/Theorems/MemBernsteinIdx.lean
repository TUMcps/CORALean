module

public import CORALean.ContSet.Taylm.Float.Operations.BernsteinIdx

@[expose] public section

/-!
# The index list holds every multi-index

Every multi-index is in `bernsteinIdx`.

## Inputs
* `n` – number of variables
* `N` – degree
* `β` – multi-index

## Hypotheses
* none

## Conclusion
* the index list holds the multi-index
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mem_bernsteinIdx (n N : ℕ) (β : Fin n → Fin (N + 1)) :
    β ∈ Taylm.bernsteinIdx n N := by -- --- PROOF ---
  induction n with
  | zero =>
    simp only [Taylm.bernsteinIdx, List.mem_singleton]
    exact funext fun i => i.elim0
  | succ n ih =>
    simp only [Taylm.bernsteinIdx, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨β 0, Fin.tail β, ih _, Fin.cons_self_tail β⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.EmptySet.Real.Operations.Lift
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.lift_` is exact

Lifting leaves the new coordinates unbounded, so the lifted set is every point whose
selected coordinates lie in the set. For `∅` that is `∅` again.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.lift_exact (E : EmptySet n) (N : ℕ) (dims : Fin n → Fin N) :
    construct (E.lift_ N dims) =
      {y : Vec ℝ N | (fun i => y (dims i) : Vec ℝ n) ∈ construct E} := by
  ext y
  exact ⟨fun h => h.elim, fun h => h.elim⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

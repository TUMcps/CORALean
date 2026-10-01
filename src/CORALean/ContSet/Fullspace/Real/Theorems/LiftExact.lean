import CORALean.ContSet.Fullspace.Real.Operations.Lift

/-!
# `Fullspace.lift_` is exact

Lifting leaves the new coordinates unbounded, so the lifted set is every point whose
selected coordinates lie in the set. For the full space that is everything.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.lift_exact (F : Fullspace n) (N : ℕ) (dims : Fin n → Fin N) :
    (F.lift_ N dims).construct =
      {y : Vec ℝ N | (fun i => y (dims i) : Vec ℝ n) ∈ F.construct} := by
  ext y
  exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

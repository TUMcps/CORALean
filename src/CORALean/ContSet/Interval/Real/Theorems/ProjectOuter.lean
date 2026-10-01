import CORALean.ContSet.Interval.Real.Operations.Project

/-!
# `Interval.project` contains the projected points

Reading the same coordinates of a member. No hypothesis, and repeated coordinates are fine.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.project_outer (I : Interval (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' I.construct ⊆ (I.project dims).construct := by
  rintro _ ⟨x, hx, rfl⟩ k
  exact hx (dims k)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

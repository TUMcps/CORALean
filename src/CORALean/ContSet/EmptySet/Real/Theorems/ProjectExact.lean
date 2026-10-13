import CORALean.ContSet.EmptySet.Real.Operations.Project
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.project` is exact

The image of `∅` under the coordinate selection `dims` is `∅`, which is what the
returned empty set in `m` dimensions denotes.
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

theorem EmptySet.project_exact (E : EmptySet n) (dims : Fin m → Fin n) :
    construct (E.project dims) =
      (fun (x : Vec ℝ n) (j : Fin m) => x (dims j)) '' construct E := by
  change (∅ : Set (Vec ℝ m)) = _ '' (∅ : Set (Vec ℝ n))
  exact (Set.image_empty _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

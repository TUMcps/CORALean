import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# A linear map passes a Minkowski sum

What carries a guarantee stated on the nominal part and on the error box
separately to the set `InflatedContSet.construct` itself: an exact statement
about a linear image, such as a relabelling of the coordinates, then needs no
widening between the two summands.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem image_add (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (A B : Set (Vec ℝ n)) :
    f '' (A + B) = f '' A + f '' B := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, (map_add f a b).symm⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add f a b⟩

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

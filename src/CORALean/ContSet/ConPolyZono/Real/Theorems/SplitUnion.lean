import CORALean.ContSet.ConPolyZono.Real.Operations.Split
import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover

/-!
# The halves of `split` cover the set, exactly

Each half is the set intersected with a box, `intersection_exact`, so the union is inside the
set; and the set is inside its box, which the two half boxes cover, each inside its
constrained polynomial zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.split_union (cPZ : ConPolyZono (Vec ℝ n)) (d : Fin n) :
    (cPZ.split d).1.construct ∪ (cPZ.split d).2.construct = cPZ.construct := by -- --- PROOF ---
  unfold ConPolyZono.split
  dsimp only
  rw [← ConPolyZono.intersection_exact, ← ConPolyZono.intersection_exact]
  apply Set.eq_of_subset_of_subset
  · exact Set.union_subset Set.inter_subset_left Set.inter_subset_left
  · intro x hx
    -- the set is in its box, which the two half boxes cover
    rcases cPZ.interval.splitAt_cover d (cPZ.interval_contains hx) with h | h
    · exact Or.inl ⟨hx, Interval.conPolyZono_contains _ h⟩
    · exact Or.inr ⟨hx, Interval.conPolyZono_contains _ h⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

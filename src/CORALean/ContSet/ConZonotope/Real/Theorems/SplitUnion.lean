module

public import CORALean.ContSet.ConZonotope.Real.Operations.Split
public import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover

@[expose] public section

/-!
# The halves of `split` cover the set, exactly

Each half is the set intersected with a box, `intersection_exact`, so the union is inside the
set; and the set is inside its box, which the two half boxes cover, each inside its
constrained zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.split_union (cZ : ConZonotope (Vec ℝ n)) (d : Fin n) :
    (cZ.split d).1.construct ∪ (cZ.split d).2.construct = cZ.construct := by -- --- PROOF ---
  unfold ConZonotope.split
  dsimp only
  rw [← ConZonotope.intersection_exact, ← ConZonotope.intersection_exact]
  apply Set.eq_of_subset_of_subset
  · exact Set.union_subset Set.inter_subset_left Set.inter_subset_left
  · intro x hx
    -- the set is in its box, which the two half boxes cover
    rcases cZ.interval.splitAt_cover d (cZ.interval_contains hx) with h | h
    · exact Or.inl ⟨hx, Interval.conZonotope_contains _ h⟩
    · exact Or.inr ⟨hx, Interval.conZonotope_contains _ h⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Split
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
public import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalConPolyZonoContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The halves of `split` cover the set, exactly

Each half is the set intersected with a box, `intersection_exact`, so the union is inside the
set; and the set is inside its box, which the two half boxes cover, each inside its
constrained polynomial zonotope.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `d` – coordinate to split along

## Hypotheses
* none

## Conclusion
* the two halves together are exactly the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.split_union (cPZ : ConPolyZono (Vec ℝ n)) (d : Fin n) : -- --- CONCL ---
    (cPZ.split d).fst.construct ∪ (cPZ.split d).snd.construct = cPZ.construct := by -- --- PROOF ---
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

module

public import CORALean.ContSet.Interval.Real.Operations.Intersection

@[expose] public section

/-!
# `Interval.intersection` is exact

Intersecting two boxes, coordinatewise and exactly: a point is in both when
each of its coordinates clears both lower bounds and stays under both upper
ones.

[1, Eq. 1]: `[x] ∩ [y] = [max(x̲, y̲), min(x̅, y̅)]`, empty when crossed.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Hypotheses
* none

## Conclusion
* the intersection box represents the intersection of the two sets

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.intersection_exact (I₁ I₂ : Interval (Vec ℝ n)) : -- --- CONCL ---
    (I₁.intersection I₂).construct = I₁.construct ∩ I₂.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro h
    refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
    · exact (max_le_iff.mp (h j).1).1
    · exact (le_min_iff.mp (h j).2).1
    · exact (max_le_iff.mp (h j).1).2
    · exact (le_min_iff.mp (h j).2).2
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨max_le (h₁ j).1 (h₂ j).1, le_min (h₁ j).2 (h₂ j).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

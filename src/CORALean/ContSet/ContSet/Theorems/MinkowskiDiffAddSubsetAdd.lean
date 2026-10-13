import CORALean.ContSet.ContSet.ContSet

/-!
# Adding a set to a Minkowski difference stays inside the sum's own difference

[1, Prop. 3]: a point `a` of `minkowskiDiff A C` already answers `∀ c ∈ C, a + c
∈ A`, so `a + b + c = (a + c) + b` lands in `A + B` for any `b ∈ B` — the same
fact the paper states with `A`, `B`, `C` named as the eventual minuend, the
part split off it, and the subtrahend.

The paper's own hypothesis `C ⊆ A` plays no role in either proof, its own or
this one: the inclusion holds regardless, so it is not asked for here.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: shifting a Minkowski difference by `B` stays inside the
difference of the shifted minuend. -/
theorem minkowskiDiff_add_subset_add (A B C : Set α) :
    minkowskiDiff A C + B ⊆ minkowskiDiff (A + B) C := by -- --- PROOF ---
  intro z hz c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
  have e : a + b + c = a + c + b := by abel
  rw [e]
  exact Set.add_mem_add (ha c hc) hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

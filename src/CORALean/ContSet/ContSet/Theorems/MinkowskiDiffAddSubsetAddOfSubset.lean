module

public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddSubsetAdd

@[expose] public section

/-!
# Prop. 3 of the Minkowski-difference paper, as printed

[1, Prop. 3] is stated for `C ⊆ A`. `minkowskiDiff_add_subset_add` proves the
inclusion with no hypothesis at all, since neither the printed proof nor ours
uses it; this is the printed statement, hypothesis included, read off it.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3], as printed: for `C ⊆ A`, shifting the difference `A ⊖ C` by `B`
stays inside `(A ⊕ B) ⊖ C`. -/
theorem minkowskiDiff_add_subset_add_of_subset (A B C : Set α) (_hCA : C ⊆ A) :
    minkowskiDiff A C + B ⊆ minkowskiDiff (A + B) C :=
  minkowskiDiff_add_subset_add A B C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

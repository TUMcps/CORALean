module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalZonotopeSubset
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Zonotope.plus` at a box is exact, [1, Prop. 2]

[1]'s Prop. 2 prints an *identity*, `Z ⊕ I = ⟨c + c_I, [G  Diag((u-l)/2)]⟩_Z`, and a
box really is a zonotope, so `PlusIntervalOuter`'s inclusion is not the whole claim.
The one hypothesis is `I.IsNonempty`: `Interval.zonotope` is the box with its bounds
swapped where they cross, and the swapped box is not empty, so without it the right
side is strictly larger than an empty left side.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: a zonotope plus a box *is* the zonotope that concatenates the box's own
generators onto it — an identity, not merely an enclosure. -/
theorem Zonotope.plus_interval_exact (Z : Zonotope (Vec ℝ n)) {I : Interval (Vec ℝ n)}
    (hI : I.IsNonempty (ι := Fin n)) :
    Z.construct + I.construct = (Z.plus I.zonotope).construct := by
  rw [← Zonotope.plus_exact]
  exact congrArg (Z.construct + ·)
    (Set.Subset.antisymm (Interval.zonotope_contains I)
      (Interval.zonotope_subset_of_isNonempty hI))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

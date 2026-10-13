module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `Zonotope.plus` at a box, [1, Prop. 2]

CORA's `zonotope + interval`: embed the box as `Interval.zonotope`, Prop. 2's own
`⟨c_I, Diag(u - c_I)⟩`, then `plus` concatenates its generators onto `Z`'s — exactly
`⟨c + c_I, [G  Diag(u - c_I)]⟩`. Outer and not exact, since `plus` alone is exact and
what falls short is `Interval.zonotope_contains`: a box whose `sup` is below its `inf`
denotes less than the zonotope built from it does.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: a zonotope plus a box lies inside the zonotope built by concatenating
the box's own generators onto it. -/
theorem Zonotope.plus_interval_outer (Z : Zonotope (Vec ℝ n)) (I : Interval (Vec ℝ n)) :
    Z.construct + I.construct ⊆ (Z.plus I.zonotope).construct := by
  rw [← Zonotope.plus_exact]
  exact Set.add_subset_add subset_rfl (Interval.zonotope_contains I)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

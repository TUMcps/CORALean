import CORALean.ContSet.Interval.Real.Operations.BoxDiff
import Mathlib.Order.Interval.Set.Basic

/-!
# The box difference is inside the set difference

[1, Prop. 3]: `I₃ ⊆ I₁ \ I₂`. Its hypothesis `I₂ ⊆ I₁` is not used: `x(i*)` lies below `l₂(i*)` or
above `u₂(i*)`, so `x ∉ I₂` whatever the boxes. The printed proof's second goal, `I₃ ∩ I₁ = ∅`,
is a slip for `I₃ ∩ I₂ = ∅`, which is what its argument shows and what is proved here.

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `boxDiff l₁ u₁ l₂ u₂ ⊆ [l₁, u₁] \ [l₂, u₂]`. -/
theorem boxDiff_subset_diff (l₁ u₁ l₂ u₂ : Fin n → ℝ) :
    boxDiff l₁ u₁ l₂ u₂ ⊆ Icc l₁ u₁ \ Icc l₂ u₂ := by -- --- PROOF ---
  rintro x ⟨hx, i, -, h⟩
  refine ⟨hx, fun hx2 => ?_⟩
  -- coordinate `i*` is strictly outside `[l₂(i*), u₂(i*)]`
  rcases h with ⟨-, -, h⟩ | ⟨-, h, -⟩
  · exact absurd (hx2.1 i) (not_le.mpr h)
  · exact absurd (hx2.2 i) (not_le.mpr h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

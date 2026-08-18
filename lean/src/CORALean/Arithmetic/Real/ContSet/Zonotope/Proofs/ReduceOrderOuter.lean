import CORALean.Arithmetic.Real.ContSet.Zonotope.Proofs.ReduceOuter

/-!
# `Zonotope.reduceOrder` over-approximates the zonotope

Two cases and no arithmetic: below the order the zonotope is returned untouched,
above it the claim is `reduce_outer` at the partition `reduceOrder` chose. Which
partition that is never enters, as there.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Zonotope.Proofs

variable {n : ℕ}

theorem reduceOrder_outer (o : ℕ) (Z : Zonotope n) :
    Z.construct ⊆ (Z.reduceOrder o).construct := by
  unfold Zonotope.reduceOrder
  split_ifs with hlt
  · exact reduce_outer Z _
  · exact subset_rfl

end CORALean.Arithmetic.Real.Zonotope.Proofs

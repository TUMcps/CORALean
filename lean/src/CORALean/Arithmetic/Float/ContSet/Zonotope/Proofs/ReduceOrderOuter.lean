import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceOuter

/-!
# `Zonotope.reduceOrder` over-approximates the zonotope

Two cases and no arithmetic, as in the exact layer: below the order the zonotope
is returned untouched, above it the claim is `reduce_outer` at the partition
`reduceOrder` chose.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem reduceOrder_outer (o : ℕ) (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ (Z.reduceOrder o).construct := by
  unfold Zonotope.reduceOrder
  split_ifs with hlt
  · exact reduce_outer Z _
  · exact subset_rfl

end CORALean.Arithmetic.Float.Zonotope.Proofs

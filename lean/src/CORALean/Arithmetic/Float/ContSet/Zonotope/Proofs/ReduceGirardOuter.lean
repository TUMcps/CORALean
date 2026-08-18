import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceByOuter

/-!
# `Zonotope.reduceGirard` over-approximates the zonotope

Two cases and no arithmetic, as in the exact layer: below the order the zonotope
is returned untouched, above it the claim is `reduceBy_outer` at the partition
the metric chose. The metric appears nowhere here, which is what lets `le` carry
no axiom.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem reduceGirard_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Arithmetic.Float.Zonotope.Proofs

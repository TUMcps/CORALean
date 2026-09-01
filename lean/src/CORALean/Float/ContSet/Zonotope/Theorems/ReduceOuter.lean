import CORALean.Float.ContSet.Zonotope.Theorems.ReduceByOuter

/-!
# `Zonotope.reduce` over-approximates the zonotope

Two cases and no arithmetic, as in the exact layer: below the order the zonotope
is returned untouched, above it the claim is `reduceBy_outer` at the partition
the metric chose. The metric appears nowhere here, which is what lets `le` carry
no axiom.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem Zonotope.reduceGirard_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope 𝕋 n) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Float

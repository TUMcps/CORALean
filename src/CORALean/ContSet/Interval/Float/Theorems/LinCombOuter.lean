import CORALean.ContSet.Interval.Float.Operations.API

/-!
# `Interval.linComb` contains every segment between the two intervals

The exact guarantee composed with the refinement, as every float guarantee is.
Here the refinement is an equality in disguise — `toReal_minimum` and
`toReal_maximum` say the stored bounds are exactly the exact ones — so no
precision is lost and the inclusion holds in both directions.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem Interval.aux_linComb_outer_refines (I₁ I₂ : Interval 𝕋 n) :
    (I₁.nominal.linComb I₂.nominal).construct ⊆ (I₁.linComb I₂).construct := by
  intro x hx i
  refine ⟨?_, ?_⟩
  · show toReal (minimum (I₁.inf i) (I₂.inf i)) ≤ x i
    rw [toReal_minimum]
    exact (hx i).1
  · show x i ≤ toReal (maximum (I₁.sup i) (I₂.sup i))
    rw [toReal_maximum]
    exact (hx i).2

theorem Interval.linComb_outer (I₁ I₂ : Interval 𝕋 n) :
    segments I₁.construct I₂.construct ⊆ (I₁.linComb I₂).construct :=
  subset_trans (Real.Interval.linComb_outer I₁.nominal I₂.nominal)
    (Interval.aux_linComb_outer_refines I₁ I₂)

end CORALean.Float

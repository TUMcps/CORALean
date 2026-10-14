module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.LinComb
public import CORALean.ContSet.Interval.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `Interval.linComb` contains every segment between the two intervals

The refinement here is an equality in disguise: `toReal_minimum` and
`toReal_maximum` say the stored bounds are exactly the exact ones, so no
precision is lost.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_linComb_outer_refines (I₁ I₂ : Interval (Vec 𝕋 n)) :
    (I₁.nominal.linComb I₂.nominal).construct ⊆ (I₁.linComb I₂).construct := by -- --- PROOF ---
  intro x hx i
  refine ⟨?_, ?_⟩
  · show toReal (minimum (I₁.inf i) (I₂.inf i)) ≤ x i
    rw [toReal_minimum]
    exact (hx i).1
  · show x i ≤ toReal (maximum (I₁.sup i) (I₂.sup i))
    rw [toReal_maximum]
    exact (hx i).2


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.linComb_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    Set.linComb I₁.construct I₂.construct ⊆ (I₁.linComb I₂).construct :=
  subset_trans (Real.Interval.linComb_outer I₁.nominal I₂.nominal)
    (Interval.aux_linComb_outer_refines I₁ I₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

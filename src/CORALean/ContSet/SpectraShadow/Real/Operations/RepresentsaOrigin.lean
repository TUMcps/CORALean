import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

/-!
# `SpectraShadow.representsa_origin`

CORA's `@spectraShadow/representsa_` at type `origin`, at tolerance `0` (where `withinTol` is
equality): every upper support `supportFunc_(SpS, ±eᵢ, 'upper')` is `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both upper supports along every axis are `0`. -/
noncomputable def SpectraShadow.representsa_origin (S : SpectraShadow (Vec ℝ n)) : Prop :=
  ∀ i : Fin n, S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) = 0
    ∧ S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

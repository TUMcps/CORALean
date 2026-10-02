import CORALean.ContSet.Taylm.Float.Operations.Const

/-!
# `Taylm.const` encloses the constant
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.const_outer (c : 𝕋) (N : ℕ) :
    (Taylm.const n c N).Encloses fun _ => toReal c := by
  intro t _
  simp [Taylm.const, Taylm.nominal, Real.Taylm.poly, Real.Taylm.monomial_zero, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Taylm.Float.Operations.Mtimes
import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter

/-!
# `Taylm.mtimes` encloses the matrix image
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

theorem Taylm.mtimes_outer {k m : ℕ} (M : Mat 𝕋 k m) {T : Fin m → Taylm 𝕋 n}
    {f : Fin m → Vec ℝ n → ℝ} (h : ∀ j, (T j).Encloses (f j)) (i : Fin k) :
    (Taylm.mtimes M T i).Encloses fun t => ∑ j, toReal (M i j) * f j t :=
  Taylm.sum_outer fun j => Taylm.smul_outer ⟨le_refl _, le_refl _⟩ (h j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

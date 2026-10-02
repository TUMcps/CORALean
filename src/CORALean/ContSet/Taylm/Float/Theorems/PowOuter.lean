import CORALean.ContSet.Taylm.Float.Operations.Pow
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
import CORALean.ContSet.Taylm.Float.Theorems.ConstOuter

/-!
# `Taylm.pow` encloses the power
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

theorem Taylm.pow_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    ∀ k : ℕ, (T.pow k).Encloses fun t => f t ^ k := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    have := Taylm.const_outer (n := n) (one : 𝕋) T.maxOrder
    rw [toReal_one] at this
    simpa only [Taylm.pow, pow_zero] using this
  | succ k ih => simpa only [Taylm.pow, pow_succ] using Taylm.times_outer ih h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

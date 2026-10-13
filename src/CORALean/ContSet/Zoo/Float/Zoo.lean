import CORALean.ContSet.Taylm.Float.Taylm
import CORALean.ContSet.Interval.Float.Interval

/-!
# Zoos over a floating-point scalar: the representation

CORA's `zoo` with its two members over `𝕋`: an optional Taylor model (`taylm(int)`) and an
optional interval, as in the exact layer's `Zoo`. A member encloses the function on the box `[-1,
1]ⁿ` through its stored floats (`nominal`): the Taylor model as `Taylm.Encloses`, the interval as
holding the function's value at every box point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Zoo (𝕋 : Type) (n : ℕ) where
  taylm : Option (Taylm 𝕋 n)
  ivl : Option (Interval (Vec 𝕋 1))

/-- Every member encloses `f` on the box. -/
def Zoo.Encloses [SoundFloatArithmetic 𝕋] (Z : Zoo 𝕋 n) (f : Vec ℝ n → ℝ) : Prop :=
  (∀ T, Z.taylm = some T → T.Encloses f) ∧
    ∀ I, Z.ivl = some I → ∀ t ∈ Real.Taylm.box n, (fun _ => f t : Vec ℝ 1) ∈ I.construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

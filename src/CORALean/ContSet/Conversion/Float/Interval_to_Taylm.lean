import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Taylm

/-!
# A box as an array of Taylor models, over a floating-point scalar

CORA's constructor `taylm(int, max_order)`: through the box's zonotope, whose generators
are the variables, so one variable per coordinate. The range set contains the box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.taylm (I : Interval (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 n :=
  I.zonotope.taylm N


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.taylm_contains (I : Interval (Vec 𝕋 n)) (N : ℕ) :
    I.construct ⊆ Taylm.construct (I.taylm N) := by
  have h := Zonotope.taylm_exact I.zonotope N
  exact fun x hx => h.symm ▸ I.zonotope_contains hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

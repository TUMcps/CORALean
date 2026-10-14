module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeTaylmExact
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A box as an array of Taylor models, over a floating-point scalar

CORA's constructor `taylm(int, max_order)`: through the box's zonotope, whose generators
are the variables, so one variable per coordinate. The range set contains the box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.taylm_contains (I : Interval (Vec 𝕋 n)) (N : ℕ) :
    I.construct ⊆ Taylm.construct (I.taylm N) := by
  have h := Zonotope.taylm_exact I.zonotope N
  exact fun x hx => h.symm ▸ I.zonotope_contains hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

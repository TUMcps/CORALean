module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.Inf`, over a floating-point scalar

CORA's `spectraShadow.Inf(n)`: the `1 × 1` inequality `1 ⪰ 0` over `n` free coefficients that
carry the unit vectors. Only the constant `one` is stored, so nothing rounds and the error box is
the origin box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spectraShadow.Inf(n)`: the `1 × 1` inequality `1 ⪰ 0` over `n` free coefficients. -/
def SpectraShadow.Inf (n : ℕ) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := 1
  m := n
  A₀ := fun _ _ => one
  A := fun _ _ _ => zero
  c := fun _ => zero
  G := fun j i => if i.val = j.val then one else zero
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

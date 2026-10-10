import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

/-!
# `SpectraShadow.empty`, over a floating-point scalar

CORA's `spectraShadow.empty(n)`: the `1 × 1` inequality `-1 ⪰ 0` over `n` free coefficients that
carry the unit vectors. Only the constant `neg one` is stored, so nothing rounds and the error box
is the origin box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spectraShadow.empty(n)`: the `1 × 1` inequality `-1 ⪰ 0` over `n` free coefficients. -/
def SpectraShadow.empty (n : ℕ) : SpectraShadow 𝕋 n where
  k := 1
  m := n
  A₀ := fun _ _ => neg one
  A := fun _ _ _ => zero
  c := fun _ => zero
  G := fun j i => if i.val = j.val then one else zero
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

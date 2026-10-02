import CORALean.Global.Float.TrigRange
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.sin`

`sinRange` on every coordinate (`Global/Float/TrigRange`): the values at the two ends where the
derivative is certified of one sign on the range, the midpoint form clamped to `[-1, 1]`
otherwise. CORA's exact case analysis on the extremal points needs `π` and a rounding to an
integer, which the scalar does not offer; the real layer's `Interval.sin` does it. `p` is the
number of halvings of the sine and cosine.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sin (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => (sinRange p (I.inf i) (I.sup i)).1
  sup := fun i => (sinRange p (I.inf i) (I.sup i)).2


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

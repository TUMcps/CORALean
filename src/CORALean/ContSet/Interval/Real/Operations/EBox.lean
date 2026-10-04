import Mathlib.Data.EReal.Basic
import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.EBox`: bounds with infinite ends

The bounds CORA's `interval.Inf`, `lift_` and `dirac` return: `inf` and `sup` in the extended
reals. `Interval` holds real bounds (`EReal` is no `AddCommGroup`, so it cannot be the ambient
type of one), so this is not an interval type: only the bound pair, and (`EBox.construct`) the
set it denotes, which the three operations need and nothing else does.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lower and upper bound per coordinate, in `EReal`. -/
abbrev Interval.EBox (n : ℕ) : Type := (Fin n → EReal) × (Fin n → EReal)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Times that are multiples of `0.5`

The test of `next`: `withinTol(mod(time,0.5),0)` with the default tolerance `1e-8` of `withinTol`.
`mod(time,0.5)` is `time - floor(time/0.5)*0.5`, in `[0,0.5)`, so `withinTol` (`abs(a-b) <= tol`;
its relative test divides by `min(abs(a),0) = 0`) holds exactly if it is at most `1e-8`: a time
slightly above a multiple of `0.5` passes and one slightly below it does not.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `withinTol(mod(time,0.5),0)`. -/
def Rtl.IsHalfMultiple (time : ℝ) : Prop :=
  time - ⌊time / (1 / 2)⌋ * (1 / 2) ≤ 1 / 10 ^ 8

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

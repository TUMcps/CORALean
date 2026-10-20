module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHiFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHi
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermFloat

@[expose] public section

/-!
# The float `quadTermHi` is at least the exact one

Each endpoint's float upper bound is at least `γ` there, and `max` is monotone.

## Inputs
* `t` – float time
* `a` – float box lower end
* `b` – float box upper end

## Hypotheses
* none

## Conclusion
* the float upper value is at least the exact greatest value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.quadTermHi_ge (t a b : 𝕋) :
    Real.MatExp.quadTermHi (toReal t) (toReal a) (toReal b) ≤
      toReal (MatExp.quadTermHi t a b) := by
  rw [MatExp.quadTermHi, toReal_maximum, Real.MatExp.quadTermHi]
  exact max_le_max (MatExp.quadTerm_mem t a).2 (MatExp.quadTerm_mem t b).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

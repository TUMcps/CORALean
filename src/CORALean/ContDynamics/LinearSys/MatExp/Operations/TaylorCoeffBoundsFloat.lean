module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat

@[expose] public section

/-!
# `MatExp.taylorCoeffBounds`, a float enclosure of `r ^ k / k!`

The scalar every order of a step scales a matrix power by: the input term's
`r^{i+1}/(i+1)!` and the correction's `r^i/i!`. An interval `[lo, hi]`, each end a
power and a reciprocal factorial rounded the same way; the reciprocal's lower
end is clamped at `zero`, which `1/k! > 0` makes free and which lets the lower
product be compared without a sign case.

## Inputs
* `r` – float step length
* `k` – order index

## Output
* float interval enclosing the Taylor coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo, hi]` with `lo ≤ r ^ k / k! ≤ hi`, for a nonnegative `r`. -/
def MatExp.taylorCoeffBounds (r : 𝕋) (k : ℕ) : Interval 𝕋 :=
  ⟨mulDown (MatExp.powDown k r) (maximum zero (MatExp.invFactorialBounds k).inf),
    mulUp (MatExp.powUp k r) (MatExp.invFactorialBounds k).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

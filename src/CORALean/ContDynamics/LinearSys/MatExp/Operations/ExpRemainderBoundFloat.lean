module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat

@[expose] public section

/-!
# `MatExp.expRemainderBound`, a float bound on the Taylor tail

`Real.MatExp.expRemainderBound`'s numerator, `‖x‖ ^ (η+1) / (η+1)!`, rounded up by
`powUp`/`divUp`/`factorialDown`'s *lower* bound of the factorial (dividing by a lower bound is
what overestimates a quotient, as in `invFactorialBounds`'s high side), times the fixed
constant `2`: sound whenever `nrm / (η+2) ≤ 1/2` (`Theorems/ExpRemainderBoundFloat`), since then
`(1 - nrm/(η+2))⁻¹ ≤ 2`. A concrete constant, not a computed reciprocal of a rounded difference,
which has no float lower bound the interface can certify positive.

## Inputs
* `nrm` – float matrix norm
* `η` – Taylor order

## Output
* float bound on the Taylor tail
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expRemainderBound (nrm : 𝕋) (η : ℕ) : 𝕋 :=
  mulUp (divUp (MatExp.powUp (η + 1) nrm) (MatExp.factorialDown (η + 1))) (addUp one one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

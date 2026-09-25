import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# `MatExp.intervalInputRemainder`, the input remainder over a float box

The `E(r)·r` of [1, Thm. 3.1] at every member of a float interval matrix: one
width for every entry, the remainder bound being on a norm, and taken at
`normUpperBound (r • A)`, the bound the exponential and the correction of the
same step are taken at, so one order is admissible for all three.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-E(r)·r, E(r)·r]` in every entry, for a nonnegative `r`. -/
def MatExp.intervalInputRemainder (A : Interval (Mat 𝕋 n n)) (r : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η  -- E(r)
  let w := mulUp r E                                                               -- E(r)·r
  ⟨fun _ _ => neg w, fun _ _ => w⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

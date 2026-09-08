import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# The matrix set order `i` contributes to the input solution

`LinearSys.inputTerm` at a set-valued matrix: `Aⁱ r^{i+1}/(i+1)!` with the
power taken over the whole box, so the result is an interval matrix and the
input set is multiplied by one of those.

`matPow` is where this loses tightness against a run at one fixed matrix: it
admits products of different members at different factors, as everywhere else
interval arithmetic takes a power.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval matrix order `i` contributes to the input solution:
`Aⁱ r^{i+1}/(i+1)!` over the whole set of system matrices. -/
noncomputable def LinParamSys.inputTerm {n : ℕ} (sys : LinParamSys ℐ n) (r : ℝ) (i : ℕ) :
    Interval (Mat ℝ n n) :=
  Interval.smul (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) (sys.A.matPow i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

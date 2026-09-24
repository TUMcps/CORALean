import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Sampling a system whose matrix was already a set

`LinearSys.discretizeEnclosure` one level up. There the discretized system is
set-valued only because `e^{AΔt}` cannot be computed; here the matrix is a box
to begin with, and `expIntervalEnclosure` of `Δt • sys.A` covers both the
uncertainty and the truncation at once. Either way the result is a
`LinParamSysDT`, so the loop of [1, Alg. 4] — `R(k) = e^{AΔt}R(k-1) ⊞ P_R(0)`,
reduced every step — is `LinParamSysDT.reach` and needs no recursion here.

`ℐ` names the family, where the point case writes it out: the argument is
already a `LinParamSys ℐ n`, so the instances arrive with the system rather
than with this definition.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The discrete-time system a step of `Δt` leaves behind, at a system matrix
that was a set already: `e^{AΔt}` enclosed over the whole box, [1, Alg. 4]. -/
noncomputable def LinParamSys.discretizeEnclosure (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ) :
    LinParamSysDT ℐ n :=
  ⟨MatExp.expIntervalEnclosure (Interval.smul Δt sys.A) η⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

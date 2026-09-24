import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure

/-!
# `e^{At}` at every matrix the set holds, as one interval matrix

`expIntervalEnclosure` of the box `t • sys.A` [1, Sec. 3.3.1], at the order
asked for raised to `reachOrder t + 2` wherever that is higher: the enclosure
holds only at an order admissible for `t`, and a window far into the horizon
needs a higher one than the first. So `exp_mem_expEnclosure` asks nothing of
`t` or of the order, only that the matrix be a member.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e^{A t}` for every `A ∈ sys.A`: the box `t • sys.A`'s exponential, at order
`η` raised until admissible for `t`. -/
noncomputable def LinParamSys.expEnclosure (sys : LinParamSys ℐ n) (t : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) :=
  let ηt := max η (sys.reachOrder t + 2)                         -- η, raised until admissible
  MatExp.expIntervalEnclosure (Interval.smul t sys.A) ηt         -- e^{[A] t}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

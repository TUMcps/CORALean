module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure

@[expose] public section

/-!
# `e^{At}` at every matrix the set holds, as one interval matrix

`expIntervalEnclosure` of the box `t • sys.A` [1, Sec. 3.1], at the order
asked for raised to `reachOrder t + 2` wherever that is higher: the enclosure
holds only at an order admissible for `t`, and a window far into the horizon
needs a higher one than the first. So `exp_mem_expEnclosure` asks nothing of
`t` or of the order, only that the matrix be a member.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

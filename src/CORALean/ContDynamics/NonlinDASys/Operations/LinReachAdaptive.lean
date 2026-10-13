module

public import CORALean.ContDynamics.NonlinDASys.Operations.PassAdaptive

@[expose] public section

/-!
# `NonlinDASys.linReachAdaptive`

CORA's `linReach_adaptive` ([1, Alg. 1]) for a start set at the finite horizon `h`: on
the last step one pass at `h`, otherwise a first run at `h` and a second at the step the tuning
`T.tune` chose from it. The heuristics are `AdaptTuning`'s arguments, the tensor order is fixed
at 2, and the extra pass of `timeStepequalHorizon` is not modelled: the second run's sets are
returned.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `linReach_adaptive` for the start set `Rstart` at the finite horizon `h`: on the last
step one pass at `h`, otherwise a first run at `h` and a second at the step size `T.tune` chose
from it. -/
noncomputable def NonlinDASys.linReachAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (Rstart : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (η fuelErr fuelHalf : ℕ) (adm_x : Vec ℝ n) (adm_y : Vec ℝ p)
    (h : ℝ) (lastStep : Bool) : Option (NonlinDASys.AdaptPass n p) :=
  let L := T.taylor Rstart                                                 -- priv_linearize
  if lastStep then
    sys.passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf h          -- last step
  else
    match sys.passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf h with  -- run 1
    | none => none
    | some p₁ =>
      sys.passAdaptive T L Rstart U η fuelErr adm_x adm_y fuelHalf (T.tune h p₁)  -- run 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

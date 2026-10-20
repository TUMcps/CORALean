module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachAdaptiveLoop

@[expose] public section

/-!
# `NonlinDASys.reachAdaptive`

CORA's `reach_adaptive` ([1, Alg. 1]): the start state `options.t = 0`, `options.R = R0`,
the finite horizon and the admissible errors, and the loop `reachAdaptiveLoop`. The union of
the time-interval sets and the time reached, `consistentInitialState` for `Rstart_y` not run (the
linearization's `y*` is `T.taylor`'s).

## Inputs
* `sys` – system
* `T` – tuning heuristics
* `R0` – start set
* `U` – input zonotope
* `tFinal` – final time
* `tol` – tolerance
* `h₀` – initial step size
* `adm_x₀` – admissible state errors
* `adm_y₀` – admissible algebraic errors
* `η` – Taylor order
* `fuelErr` – error loop fuel
* `fuelHalf` – step halving fuel
* `fuel` – iteration bound

## Output
* the union of the time-interval sets and the time reached, or none

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

/-- CORA's `reach_adaptive`: the union of the time-interval sets from `R0` to `tFinal`, and the
time reached, or `none` where `fuel` or a step ran out. -/
noncomputable def NonlinDASys.reachAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (R0 : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m))
    (tFinal tol h₀ : ℝ) (adm_x₀ : Vec ℝ n) (adm_y₀ : Vec ℝ p) (η fuelErr fuelHalf fuel : ℕ) :
    Option (Set (Vec ℝ n) × ℝ) :=
  let st : NonlinDASys.AdaptState n p :=                                  -- options.t, .R, ...
    { t := 0, R := R0, h := h₀, adm_x := adm_x₀, adm_y := adm_y₀ }
  sys.reachAdaptiveLoop T U tFinal tol η fuelErr fuelHalf fuel st ∅          -- while

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

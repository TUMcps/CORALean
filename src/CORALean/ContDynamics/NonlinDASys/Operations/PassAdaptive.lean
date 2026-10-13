import CORALean.ContDynamics.NonlinDASys.Operations.ErrorLoopAdaptive

/-!
# `NonlinDASys.passAdaptive`

One pass of CORA's `linReach_adaptive` ([1, Alg. 1]) at the step `Δt`: the error loop,
and the step halved (`options.Δt * 0.5`) where it did not converge, `fuel` times.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One pass at the step `Δt`: the error loop, and the step halved (`options.Δt * 0.5`)
where it did not converge. -/
noncomputable def NonlinDASys.passAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (L : NonlinDASys.LinPoint n p m)
    (Rstart : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (η fuelErr : ℕ)
    (adm_x : Vec ℝ n) (adm_y : Vec ℝ p) :
    ℕ → ℝ → Option (NonlinDASys.AdaptPass n p)
  | 0, _ => none
  | k + 1, Δt =>
    match sys.errorLoopAdaptive T L Rstart U Δt η fuelErr adm_x adm_y with
    | some err => some ⟨Δt, err⟩
    | none => sys.passAdaptive T L Rstart U η fuelErr adm_x adm_y k (Δt / 2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

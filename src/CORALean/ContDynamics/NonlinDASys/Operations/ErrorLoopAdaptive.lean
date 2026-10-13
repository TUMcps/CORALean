module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
public import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# `NonlinDASys.errorLoopAdaptive`

The `while` loop on the abstraction error of CORA's `linReach_adaptive` ([1, Alg. 1]):
boxes of the admissible error, the pass over them, the abstraction error over its joint set,
accepted where it fits and run again at `expFactor` times it where it does not. Both `Verror`
and `priv_abstractionError_adaptive` subtract `CF_inv` times the algebraic error where CORA adds
it (FINDINGS.md). The linear part and `errorSolution_adaptive` are one `oneStep` at
`U_lin ⊕ Verror`, as in `linReach`; `fuel` replaces the loop and its divergence test.

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

/-- The `while` loop on the abstraction error of `linReach_adaptive`: boxes of the admissible
error `adm_x`, `adm_y`, the pass over them, the abstraction error over its joint set, accepted
where it fits and run again at `expFactor` times it where it does not. -/
noncomputable def NonlinDASys.errorLoopAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (L : NonlinDASys.LinPoint n p m)
    (Rstart : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (η : ℕ) :
    ℕ → Vec ℝ n → Vec ℝ p → Option (NonlinDASys.AbstractionError n p)
  | 0, _, _ => none
  | fuel + 1, adm_x, adm_y =>
    let Verror_x : Zonotope (Vec ℝ n) :=   -- 0 +- adm_x
      Interval.zonotope ⟨-adm_x, adm_x⟩
    let Verror_y : Zonotope (Vec ℝ p) :=   -- 0 +- adm_y
      Interval.zonotope ⟨-adm_y, adm_y⟩
    let Verror : Zonotope (Vec ℝ n) :=                                     -- Verror, sign corrected
      Verror_x.plus (Verror_y.mtimes (-(L.C * L.F_inv)))
    let R := NonlinDASys.linReachAt sys { L with Verror := Verror, Verror_y := Verror_y }
      Rstart U Δt η                                                        -- Rmax and R_y
    let err := NonlinDASys.abstractionErrorAdaptive (L.C * L.F_inv)        -- abstractionError
      (T.hess R.2.2)
    if (List.finRange n).all (fun i => T.le (err.errorInt_x i / adm_x i) 1) &&
        (List.finRange p).all (fun j => T.le (err.errorInt_y j / adm_y j) 1) then
      some err                                                             -- perfIndCurr <= 1
    else
      sys.errorLoopAdaptive T L Rstart U Δt η fuel                         -- expFactor * errorInt
        (T.expFactor • err.errorInt_x) (T.expFactor • err.errorInt_y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

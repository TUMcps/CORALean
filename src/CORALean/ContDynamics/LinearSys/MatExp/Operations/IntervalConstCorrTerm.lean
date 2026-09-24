import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: one order's contribution to the integrated correction over a box

`intervalConstCorrTerm`: what order `i` contributes to [1]'s constant correction over a whole
box: `constCorrTerm`'s scalar factor against the box the `(i+1)`-th power lies in.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What order `i` contributes to the constant correction over a whole box:
`constCorrTerm`'s scalar factor against the box the `(i+1)`-th power lies in. -/
noncomputable def MatExp.intervalConstCorrTerm (A : Interval (Mat ℝ n n)) (r : ℝ) (i : ℕ) :
    Interval (Mat ℝ n n) :=
  Interval.smul (MatExp.corrCoeff (i + 2) * r ^ (i + 2) * ((Nat.factorial (i + 2) : ℝ))⁻¹)
    (A.matPow (i + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: one order's contribution to the integrated correction over a box

`intervalConstCorrTerm`: what order `i` contributes to [1, Sec. III-A]'s constant correction over a
whole box: `constCorrTerm`'s scalar factor against the box the `(i+1)`-th power lies in.

## Inputs
* `A` – interval matrix
* `r` – step length
* `i` – order index

## Output
* interval matrix of the order's integrated correction term

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

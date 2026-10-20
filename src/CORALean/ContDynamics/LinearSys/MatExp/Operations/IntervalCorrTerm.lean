module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: one order's contribution to the correction over a box

`intervalCorrTerm`: what order `i` contributes to [1]'s correction over a whole box:
`corrTerm`'s scalar factor against the box the `i`-th power lies in.

The finite orders are CORA's `priv_tie` of `@linParamSys`: the interval
`[corrCoeff i, 0]` times the box `matPow A i`, multiplied in by `Interval.smul`,
`min`/`max` against zero being the second endpoint's contribution. `matPow` is
the dependency loss, as in `IntervalEnclosures`: it admits products of
different members at each factor.

## Inputs
* `A` – interval matrix
* `r` – step length
* `i` – order index

## Output
* interval matrix of the order's correction term over the box

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What order `i` contributes to the correction over a whole box: `corrTerm`'s
scalar factor against the box the `i`-th power lies in. -/
noncomputable def MatExp.intervalCorrTerm (A : Interval (Mat ℝ n n)) (r : ℝ) (i : ℕ) :
    Interval (Mat ℝ n n) :=
  Interval.smul (MatExp.corrCoeff i * r ^ i * ((Nat.factorial i : ℝ))⁻¹) (A.matPow i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

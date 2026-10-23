module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical

@[expose] public section

/-!
# The correction's coefficient

`corrCoeff`: how far below zero `s ^ i - s` reaches on `[0,1]`. [1, Thm. 3] writes this
`i^(-i/(i-1)) - i^(-1/(i-1))`, which `aux_corrCoeff_eq` confirms; in this form the
exponent is a natural number and the bound is provable as stated.

## Inputs
* `i` – order

## Output
* how far below zero the correction polynomial reaches

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far below zero `s ^ i - s` reaches on `[0,1]`. [1, Thm. 3] writes this
`i^(-i/(i-1)) - i^(-1/(i-1))`, which `aux_corrCoeff_eq` confirms; in this form the
exponent is a natural number and the bound is provable as stated. -/
noncomputable def MatExp.corrCoeff (i : ℕ) : ℝ :=
  MatExp.corrCritical i ^ i - MatExp.corrCritical i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

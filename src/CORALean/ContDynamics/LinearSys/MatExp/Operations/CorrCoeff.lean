import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCritical

/-!
# The correction's coefficient

`corrCoeff`: how far below zero `s ^ i - s` reaches on `[0,1]`. [1] writes this
`i^(-i/(i-1)) - i^(-1/(i-1))`, which `aux_corrCoeff_eq` confirms; in this form the
exponent is a natural number and the bound is provable as stated.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far below zero `s ^ i - s` reaches on `[0,1]`. [1] writes this
`i^(-i/(i-1)) - i^(-1/(i-1))`, which `aux_corrCoeff_eq` confirms; in this form the
exponent is a natural number and the bound is provable as stated. -/
noncomputable def MatExp.corrCoeff (i : ℕ) : ℝ :=
  MatExp.corrCritical i ^ i - MatExp.corrCritical i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff

/-!
# What one order contributes to the integrated correction

`constCorrTerm`: [1]'s order `i+2` contribution to the *integrated* correction. The same shape
as `corrTerm`, one factorial further along and one matrix power back, which is what
integrating each order of the exponential does to it.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What order `i+2` contributes to the *integrated* correction. The same shape
as `corrTerm`, one factorial further along and one matrix power back, which is
what integrating each order of the exponential does to it. -/
noncomputable def MatExp.constCorrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) :
    ℝ :=
  MatExp.corrCoeff (i + 2) * r ^ (i + 2)
    * (((Nat.factorial (i + 2) : ℝ))⁻¹ * (A ^ (i + 1)) j k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

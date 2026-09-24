import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff

/-!
# What one order contributes to the correction

`corrTerm`: what order `i` contributes to [1]'s correction, at the far end of its range.
The interval it spans is between this and zero, on whichever side its sign puts it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What order `i` contributes to the correction, at the far end of its range.
The interval it spans is between this and zero, on whichever side its sign puts
it. -/
noncomputable def MatExp.corrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) : ℝ :=
  MatExp.corrCoeff i * r ^ i * (((Nat.factorial i : ℝ))⁻¹ * (A ^ i) j k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

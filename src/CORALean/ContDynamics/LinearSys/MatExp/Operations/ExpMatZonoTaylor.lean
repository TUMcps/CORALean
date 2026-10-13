module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTerm
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# Matrix zonotopes: the Taylor truncation

`expMatZonoTaylor`: [1, Sec. 3.3.2]'s Taylor truncation as a matrix zonotope, `i = 0 … η`
matching `MatExp.expTaylor`'s `Finset.range (η + 1)` exactly — `expIntervalTaylor`'s recursion
at a zonotope, so that the correlations between a system matrix's entries survive the powers.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor truncation as a matrix zonotope, `i = 0 … η` matching
`MatExp.expTaylor`'s `Finset.range (η + 1)` exactly. -/
noncomputable def MatExp.expMatZonoTaylor (M : Zonotope (Mat ℝ n n)) :
    ℕ → Zonotope (Mat ℝ n n)
  | 0 => MatExp.expMatZonoTerm M 0
  | k + 1 => Zonotope.plus (MatExp.expMatZonoTerm M (k + 1)) (MatExp.expMatZonoTaylor M k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

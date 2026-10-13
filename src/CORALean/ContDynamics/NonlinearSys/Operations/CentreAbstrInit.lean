module

public import CORALean.ContDynamics.NonlinearSys.Definitions.CentreAbstrState

@[expose] public section

/-!
# `Alg. 1` line 1, linearizing at the centre

`centreAbstrInit`: [1, Alg. 1] line 1 and the algorithm's input `R(t_0) = X₀`, before the
first iteration.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}
variable {S : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1 and the algorithm's input `R(t_0) = X₀`, before the first iteration. -/
def NonlinearSys.centreAbstrInit (X₀ : S n) : NonlinearSys.CentreAbstrState S n :=
  { t := 0                                                       -- 1. s = 0, t_s = 0
    R := X₀
    Rτ := X₀ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

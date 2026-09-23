import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrState

/-!
# `Alg. 1` line 1: the loop state before the first iteration

`abstrInit`: [1, Alg. 1] line 1 and the algorithm's input `R(t_0) = X₀`, before the first
iteration.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}
variable {S : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1 and the algorithm's input `R(t_0) = X₀`, before the first iteration. -/
def NonlinearSys.abstrInit (X₀ : S n) : NonlinearSys.AbstrState S n :=
  { t := 0                                                       -- 1. k ← 0, t_k ← 0
    R := X₀
    Rτ := X₀ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

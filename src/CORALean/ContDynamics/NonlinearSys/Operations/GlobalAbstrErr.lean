module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.BoxDiameter

@[expose] public section

/-!
# The global accumulated abstraction error of a set-based solver

`[1, Def. 4]`, equation (29): what a whole run of `N` steps has added to the exact answer,
measured on the Minkowski difference `R(t_end) ⊖ R̂(t_end)` of the run's output and the same run
with the abstraction errors left out. A Minkowski difference and not a subtraction of
representations: `⊖` strips `R̂` off `R` without either set having to be named by a zonotope.
`minkowskiDiff` is `{x | ∀ y ∈ R̂, x + y ∈ R}`, so an `R̂` that is not enclosed by `R` yields the
empty set and, with it, `boxDiameter`'s junk value rather than an error.

## Inputs
* `R` – the run's output
* `Rhat` – the run without abstraction errors

## Output
* the widest box side of the added error

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ε_N`: the widest side of the box over what `N` steps of the solver have
added to the abstraction-error-free run `R̂`. -/
noncomputable def globalAbstrErr (R Rhat : Set (Vec ℝ n)) : ℝ :=
  ‖boxDiameter (minkowskiDiff R Rhat)‖

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

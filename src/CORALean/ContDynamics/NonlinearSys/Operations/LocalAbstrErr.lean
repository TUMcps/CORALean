import CORALean.Global.BoxDiameter

/-!
# The local abstraction error of a set-based solver

`[1, Def. 4]`, equation (28): how much one step of a set-based solver adds to
the exact answer, measured as the largest side of the box over the step's set of
abstraction errors. The norm is the supremum norm, which is the one `Vec ℝ n`
already carries, so no conversion is needed here.

Stated of the step's abstraction-error set alone, which is the form the rest of
the paper uses. The paper's other form, `d(box(R ⊖ R̂))`, is `globalAbstrErr`
read at one step; `globalAbstrErr_eq_localAbstrErr` is where the two are shown
to agree, and says which hypotheses that costs.

Not a function of a `NonlinearSys`: `[1, Def. 4]` measures whatever a solver
returns, and asks nothing of how the set was produced.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `εₖ,ₗₒ꜀`: the widest side of the box over the abstraction errors one step
commits. -/
noncomputable def localAbstrErr (Rabs : Set (Vec ℝ n)) : ℝ := ‖boxDiameter Rabs‖

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

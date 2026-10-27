module

public import CORALean.Global.BoxDiameter

@[expose] public section

/-!
# The local abstraction error of a set-based solver

`[1, Def. 4]`, equation (28): how much one step of a set-based solver adds to the exact answer,
measured as the largest side of the box over the step's set of abstraction errors, in the
supremum norm `Vec ℝ n` already carries. Stated of the step's abstraction-error set alone. The
paper's other form, `d(box(R ⊖ R̂))`, is `globalAbstrErr` at one step;
`globalAbstrErr_eq_localAbstrErr` shows they agree. Not a function of a `NonlinearSys`:
`[1, Def. 4]` measures whatever a solver returns.

## Inputs
* `Rabs` – step's abstraction errors

## Output
* the widest side of their box

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
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

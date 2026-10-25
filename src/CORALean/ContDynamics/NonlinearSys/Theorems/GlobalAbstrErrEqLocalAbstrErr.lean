module

public import CORALean.ContDynamics.NonlinearSys.Operations.GlobalAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Operations.LocalAbstrErr
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The two forms `[1, Def. 4]` gives the local abstraction error

`[1, (28)]` writes `d(box(R ⊖ R̂))` and `d(box(R_abs))` as the same number, on the strength of
`R = R̂ ⊕ R_abs`. Only one direction is free: `⊖` undoes `⊕` up to a containment,
`R_abs ⊆ (R̂ ⊕ R_abs) ⊖ R̂`, and the reverse is Rådström cancellation, which asks `R_abs` to be
convex and closed and `R̂` to be nonempty and bounded. The hypotheses are stated here rather than
built into the definitions, since every step of `[1, Alg. 1]` meets them. Equality of the two
*sets* is what is proved; the error identity is that read through `boxDiameter` and the norm.

## Inputs
* `Rhat` – error-free run
* `Rabs` – abstraction error set

## Hypotheses
* `hne` – run nonempty
* `hb` – run bounded
* `hconv` – error set convex
* `hcl` – error set closed

## Conclusion
* the global error of one step equals the local error

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, (28)]`: measured on `R̂ ⊕ R_abs` against `R̂`, the global error of one
step is the local one. -/
theorem globalAbstrErr_eq_localAbstrErr {Rhat Rabs : Set (Vec ℝ n)} (hne : Rhat.Nonempty)
    (hb : Bornology.IsBounded Rhat) (hconv : Convex ℝ Rabs) (hcl : IsClosed Rabs) : -- --- CONCL ---
    globalAbstrErr (Rhat + Rabs) Rhat = localAbstrErr Rabs := by -- --- PROOF ---
  have hset : minkowskiDiff (Rhat + Rabs) Rhat = Rabs := by
    refine subset_antisymm ?_ ?_
    -- Rådström, on the outer approximation `R̂ ⊕ R_abs ⊆ R_abs ⊕ R̂` that commutativity gives
    · exact minkowskiDiff_inner_of_outer hne hb hconv hcl (add_comm Rhat Rabs).subset
    -- the free direction: `X ⊆ S ⊖ T` is `X ⊕ T ⊆ S`, again commutativity
    · exact (subset_minkowskiDiff_iff Rabs (Rhat + Rabs) Rhat).2 (add_comm Rabs Rhat).subset
  rw [globalAbstrErr, localAbstrErr, hset]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CORALean.ContSet.Interval.Real.Operations.Sinh
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.sinh` is exactly the image under `Real.sinh`

The hyperbolic sine is strictly increasing and continuous on all of `ℝ`, so
`Interval.monotoneImage_exact` applies. No domain condition.

[1, Eq. 7].

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the hyperbolic sine box is exactly the image of `I`

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sinh_exact (I : Interval (Vec ℝ n)) :
    I.sinh.construct = (fun x i => Real.sinh (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.sinh (Set.univ) Set.ordConnected_univ
    (fun a _ b _ h => Real.sinh_strictMono h) (Real.continuous_sinh.continuousOn)
    I (fun i => ⟨trivial, trivial⟩)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

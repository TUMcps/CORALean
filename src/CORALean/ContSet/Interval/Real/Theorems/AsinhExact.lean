module

public import CORALean.ContSet.Interval.Real.Operations.Asinh
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.asinh` is exactly the image under `Real.arsinh`

The inverse hyperbolic sine is strictly increasing and continuous on all of `ℝ`, so
`Interval.monotoneImage_exact` applies. No domain condition.

[1, Eq. 8].

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the inverse hyperbolic sine box is exactly the image of `I`

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
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

theorem Interval.asinh_exact (I : Interval (Vec ℝ n)) :
    I.asinh.construct = (fun x i => Real.arsinh (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.arsinh (Set.univ) Set.ordConnected_univ
    (fun a _ b _ h => Real.arsinh_strictMono h) (Real.continuous_arsinh.continuousOn)
    I (fun i => ⟨trivial, trivial⟩)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

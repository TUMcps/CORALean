import CORALean.ContSet.Interval.Real.Operations.Sqrt
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

/-!
# `Interval.sqrt` is exactly the image under `Real.sqrt`

The square root is increasing on `[0, ∞)`, so `Interval.monotoneImage_exact` applies. CORA throws
`outOfDomain` when a lower bound is negative (and returns NaN internally); here the domain is a
hypothesis, both corners nonnegative.

[1, Eq. 5], its first case.

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

theorem Interval.sqrt_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, 0 ≤ I.inf i ∧ 0 ≤ I.sup i) :
    I.sqrt.construct = (fun x i => Real.sqrt (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.sqrt (Set.Ici 0) Set.ordConnected_Ici
    (fun a ha b _ h => Real.sqrt_lt_sqrt ha h) (Real.continuous_sqrt.continuousOn) I (hI)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

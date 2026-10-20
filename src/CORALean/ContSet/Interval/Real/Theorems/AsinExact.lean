module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.asin` is exactly the image under `Real.arcsin`

The arcsine is strictly increasing on `[-1, 1]`, so `Interval.monotoneImage_exact` applies. CORA
returns a complex or NaN result outside `[-1, 1]`; here the domain is a hypothesis, both corners
in `[-1, 1]`.

[1, Eq. 6], its first case.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – bounds within `[-1, 1]`

## Conclusion
* the arcsine box is exactly the image of `I`

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

theorem Interval.asin_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, (-1 ≤ I.inf i ∧ I.inf i ≤ 1) ∧ (-1 ≤ I.sup i ∧ I.sup i ≤ 1)) :
    I.asin.construct = (fun x i => Real.arcsin (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.arcsin (Set.Icc (-1) 1) Set.ordConnected_Icc
    (Real.strictMonoOn_arcsin) (Real.continuous_arcsin.continuousOn) I (hI)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

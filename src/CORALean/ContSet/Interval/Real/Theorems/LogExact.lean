module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.log` is exactly the image under `Real.log`

The logarithm is increasing on `(0, ∞)`, so `Interval.monotoneImage_exact` applies. CORA returns
`-Inf` at `0` and throws `outOfDomain` below it; `Real.log 0 = 0` is junk, so the domain is a
hypothesis, both corners positive.

[1, Eq. 5], its first case, at `x̲ > 0`.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – bounds positive

## Conclusion
* the logarithm box is exactly the image of `I`

## References

* [1] [M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16.
      3rd International Workshop on Applied Verification for Continuous and Hybrid Systems,
      2017.](../../../../../../references/2017/althoff-arch-interval-arithmetic.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.log_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, 0 < I.inf i ∧ 0 < I.sup i) :
    I.log.construct = (fun x i => Real.log (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.log (Set.Ioi 0) Set.ordConnected_Ioi
    (Real.strictMonoOn_log) (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)) I (hI)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

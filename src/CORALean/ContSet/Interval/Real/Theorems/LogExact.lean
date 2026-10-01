import CORALean.ContSet.Interval.Real.Operations.Log
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

/-!
# `Interval.log` is exactly the image under `Real.log`

The logarithm is increasing on `(0, ∞)`, so `Interval.monotoneImage_exact` applies. CORA returns
`-Inf` at `0` and throws `outOfDomain` below it; `Real.log 0 = 0` is junk, so the domain is a
hypothesis, both corners positive.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

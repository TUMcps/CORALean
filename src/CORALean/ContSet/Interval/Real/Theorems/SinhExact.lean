import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import CORALean.ContSet.Interval.Real.Operations.Sinh
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

/-!
# `Interval.sinh` is exactly the image under `Real.sinh`

The hyperbolic sine is strictly increasing and continuous on all of `ℝ`, so
`Interval.monotoneImage_exact` applies. No domain condition.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

import CORALean.ContSet.Interval.Real.Operations.Tan
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# `Interval.tan` is exactly the image under `Real.tan`

The tangent is strictly increasing and continuous on `(-π/2, π/2)`, so
`Interval.monotoneImage_exact` applies. CORA accepts any box: it returns `(-Inf, Inf)` for one
that is at least `π` wide or contains a pole at an odd multiple of `π/2`, and otherwise evaluates
`tan` at the bounds. The statement here covers the principal branch, both corners in
`(-π/2, π/2)`, as a hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.tan_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, (-(Real.pi / 2) < I.inf i ∧ I.inf i < Real.pi / 2) ∧
      (-(Real.pi / 2) < I.sup i ∧ I.sup i < Real.pi / 2)) :
    I.tan.construct = (fun x i => Real.tan (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    Set.ordConnected_Ioo Real.strictMonoOn_tan Real.continuousOn_tan_Ioo I hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

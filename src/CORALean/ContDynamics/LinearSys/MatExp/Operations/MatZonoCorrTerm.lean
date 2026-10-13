import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Smul
import CORALean.ContSet.Zonotope.Real.Operations.MatPow

/-!
# Matrix zonotopes: one order's contribution to the correction

`intervalCorrTerm` with the power taken as a matrix zonotope and only then boxed:
CORA's `priv_tie` of `@linParamSys`, which converts `power.zono{i}` to an
interval matrix (`intervalMatrix(obj.power.zono{i})`) before multiplying it by
`[corrCoeff i, 0]`. The box of the zonotope power keeps the dependency between a
member's own factors that `Interval.matPow` loses, so it is no wider than
`matPow` of the boxed matrix zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `corrCoeff i · r^i/i!` times the box of the `i`-th matrix-zonotope power. -/
noncomputable def MatExp.matZonoCorrTerm (M : Zonotope (Mat ℝ n n)) (r : ℝ) (i : ℕ) :
    Interval (Mat ℝ n n) :=
  let Mi := (M.matPow i).interval                                  -- intervalMatrix(power.zono{i})
  Interval.smul (MatExp.corrCoeff i * r ^ i * ((Nat.factorial i : ℝ))⁻¹) Mi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

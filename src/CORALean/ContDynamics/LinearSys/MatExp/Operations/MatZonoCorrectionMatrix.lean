module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrTerm
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# Matrix zonotopes: the correction matrix

`intervalCorrectionMatrix`'s counterpart at a matrix zonotope, CORA's `priv_tie`
of `@linParamSys` with `obj.A` a `matZonotope`: orders `2` through `η` from
`matZonoCorrTerm`, each the box of a matrix-zonotope power, and everything past
`η` in the tail bound at the box of `r • M`. The result is an interval matrix, as
CORA's `obj.F` is: CORA boxes the powers before the correction, not after.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of `priv_tie` at a matrix zonotope: orders `2 … η` and the tail. -/
noncomputable def MatExp.matZonoCorrectionMatrix (M : Zonotope (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1),
      min ((MatExp.matZonoCorrTerm M r (i + 2)).inf j k) 0)
    - MatExp.expRemainderBound (Interval.smul r M.interval).absMax η
  sup := fun j k => (∑ i ∈ Finset.range (η - 1),
      max ((MatExp.matZonoCorrTerm M r (i + 2)).sup j k) 0)
    + MatExp.expRemainderBound (Interval.smul r M.interval).absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

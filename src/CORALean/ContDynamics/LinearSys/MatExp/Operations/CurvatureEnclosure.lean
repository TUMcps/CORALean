import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `C`, the curvature enclosure

`curvatureEnclosure`: Line 8 of [1, Alg. 1] — `F(Δt,η)H(t_k) ⊕ G(Δt,η)ũ`, whose two interval
matrices are already this tree's `correctionMatrix` and `constCorrectionMatrix`.
`Zonotope.mtimesIntervalMat` is CORA's own `mtimes` at an interval matrix, so `C` is the set
Line 8 computes rather than the exact product it encloses.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 8 of [1, Alg. 1]: the curvature enclosure `C = F(Δt,η)H(t_k) ⊕ G(Δt,η)ũ`. -/
noncomputable def MatExp.curvatureEnclosure (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  (Zonotope.mtimesIntervalMat (MatExp.correctionMatrix A Δt η) H).plus
    (Zonotope.mtimesIntervalMat (MatExp.constCorrectionMatrix A Δt η) (Zonotope.ofPoint ũ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

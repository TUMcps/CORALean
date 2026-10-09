import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# `MatExp.curvatureEnclosure` in floats: line 8 of [1, Alg. 1]

`C = F(Δt,η) H(t_k) ⊕ G(Δt,η) ũ` of eq. (15)-(16), with `F` and `G` the float interval
matrices `intervalCorrectionMatrix` and `intervalConstCorrectionMatrix`, each rounded outward.
Both are interval matrices, so the products are `Mtimes` at the interval-matrix family, and
`ũ` enters as the point zonotope `{ũ}`.

The real `Real.MatExp.curvatureEnclosure` takes `G` from `constCorrectionMatrix`, a point
matrix the float layer has no place for; `intervalConstCorrectionMatrix` is its enclosure at the
box `A`, so this is the same true object, enclosed (`curvatureEnclosure_outer`), and not a
different enclosure such as the input solution of the segment `[0, ũ]`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 8 of [1, Alg. 1]: the curvature enclosure `C = [F] H(t_k) ⊕ [G] {ũ}`. -/
def MatExp.curvatureEnclosure (A : Interval (Mat 𝕋 n n)) (H : Zonotope 𝕋 n) (ũ : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : Zonotope 𝕋 n :=
  let F := MatExp.intervalCorrectionMatrix A Δt η                     -- [F(Δt,η)]
  let G := MatExp.intervalConstCorrectionMatrix A Δt η                -- [G(Δt,η)]
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) F H ⊞         -- [F] H(t_k) ⊕
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) G (Interval.point ũ).zonotope  -- [G] ũ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `MatExp.curvatureEnclosure` in floats: line 8 of [1, Alg. 1]

`C = F(Δt,η) H(t_k) ⊕ G(Δt,η) ũ` of eq. (15)-(16), with `F` and `G` the float interval matrices
`intervalCorrectionMatrix` and `intervalConstCorrectionMatrix`, each rounded outward. The
products are `Mtimes` at the interval-matrix family, and `ũ` enters as the point zonotope `{ũ}`.
The real `Real.MatExp.curvatureEnclosure` takes `G` from `constCorrectionMatrix`, a point matrix
the float layer has no place for; `intervalConstCorrectionMatrix` is its enclosure at the box
`A`, so this is the same true object, enclosed (`curvatureEnclosure_outer`).

## Inputs
* `A` – float interval matrix
* `H` – float state zonotope
* `ũ` – float constant input
* `Δt` – float step length
* `η` – Taylor order

## Output
* float zonotope enclosing the curvature of the step

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 8 of [1, Alg. 1]: the curvature enclosure `C = [F] H(t_k) ⊕ [G] {ũ}`. -/
def MatExp.curvatureEnclosure (A : Interval (Mat 𝕋 n n)) (H : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : Zonotope (Vec 𝕋 n) :=
  -- 8. C ← [F(Δt,η)] H(t_k) ⊕ [G(Δt,η)] ũ, from the two interval matrices
  let F := MatExp.intervalCorrectionMatrix A Δt η                     -- [F(Δt,η)]
  let G := MatExp.intervalConstCorrectionMatrix A Δt η                -- [G(Δt,η)]
  Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [F] H(t_k) ⊕
    (S := 𝒵[𝕋]) F H ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [G] ũ
      (S := 𝒵[𝕋]) G (Interval.point ũ).zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.Operations.AffineTimeIntervalOuterFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AffineTimePointNextFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AffineWindowFloatOuter

@[expose] public section

/-!
# The float affine time-interval set holds the affine flow over the step

`affineWindowFloat_outer` at `H(t_{k+1}) = [e^{AΔt}] H ⊕ P^u(Δt)`, which holds the flow's
value one step on (`affineTimePointNextFloat_outer`): a point of `H(t_k)` under the constant
input `ũ` is, after any `τ ∈ [0, Δt]`, in `affineTimeIntervalOuterFloat`.

## Inputs
* `sys` – linear system
* `H` – float state zonotope
* `ũ` – float constant input
* `Δt` – float step length
* `η` – Taylor order
* `h` – state point
* `τ` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `hh` – point lies in the zonotope
* `hτ0` – time nonnegative
* `hτ` – time within the step

## Conclusion
* the affine flow state at the time lies in the float time-interval set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.affineTimeIntervalOuterFloat_outer (sys : LinearSys 𝕋 n) {H : Zonotope (Vec 𝕋 n)}
    {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {h : Vec ℝ n} (hh : h ∈ H.construct) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ toReal Δt) : -- --- CONCL ---
    exp (τ • Scalar.toRealMat sys.A) *ᵥ h
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) τ *ᵥ toRealVec ũ
      ∈ (sys.affineTimeIntervalOuterFloat H ũ Δt η).construct :=
  sys.affineWindowFloat_outer hΔt hη hh (sys.affineTimePointNextFloat_outer hΔt hη hh) hτ0 hτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

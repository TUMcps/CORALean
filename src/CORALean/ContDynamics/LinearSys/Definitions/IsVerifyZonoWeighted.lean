module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoState
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# What the zonotope verification pass keeps true at `t_k` in a Lyapunov weight

For every certificate `(P, L, a)` of `cert` that `Krylov.lyapunovCertificateFloat` accepts, the
gauge `ν(x) = √(x'Px)` bounds the errors of the state of `LinearSys.verifyZonotopePassFloat` at `t`
as `LinearSys.IsVerifyZonoInvariant` bounds them in the scales `s`:
* the error `e^{tA}(c₀ + G₀ b) + (∫₀ᵗ e^{σA} dσ) u₀ - (c + G b)` has `ν ≤ β` for every
  `b ∈ [-1, 1]^m`;
* `(e^{tA} - Φ) x` has `ν ≤ ψ a` for every `x` with `|x_k| ≤ a s_k`;
and both bounds are nonnegative.

## Inputs
* `sys` – linear system
* `cert` – float Lyapunov certificate `(P, L, a)` of `A`, if any
* `s` – positive scales
* `c₀` – center of the initial set
* `G₀` – generators of the initial set
* `u₀` – constant input
* `t` – time
* `st` – float state of the pass

## Output
* whether the state's errors are within its weighted bounds at `t`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state's errors at `t` are within `β` and `ψ` in the gauge of every accepted `P`. -/
def LinearSys.IsVerifyZonoWeighted (sys : LinearSys 𝕋 n) (cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋))
    (s : Vec ℝ n) (c₀ : Vec ℝ n) (G₀ : Mat ℝ n m) (u₀ : Vec ℝ n) (t : ℝ)
    (st : LinearSys.VerifyZonoState 𝕋 n m) : Prop :=
  ∀ P L a, (P, L, a) ∈ cert → (Krylov.lyapunovCertificateFloat sys.A P L a).ok = true →
  0 ≤ toReal st.β ∧ 0 ≤ toReal st.ψ ∧
  (∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
    let e := exp (t • toRealMat sys.A) *ᵥ (c₀ + G₀ *ᵥ b)
      + Real.MatExp.expIntegral (toRealMat sys.A) t *ᵥ u₀ - (toRealVec st.c + toRealMat st.G *ᵥ b)
    Real.sqrt (e ⬝ᵥ (toRealMat P *ᵥ e)) ≤ toReal st.β) ∧
  ∀ a : ℝ, 0 ≤ a → ∀ x : Vec ℝ n, (∀ k, |x k| ≤ a * s k) →
    let y := (exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ x
    Real.sqrt (y ⬝ᵥ (toRealMat P *ᵥ y)) ≤ toReal st.ψ * a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

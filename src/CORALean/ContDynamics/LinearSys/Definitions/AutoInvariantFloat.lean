module

public import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# What an `Alg. 2` state owes at `t_k`, in floats

`AutoInvariantFloat`: the state of a run from `X₀` under inputs in `V` holds, at `t_k`, the time
bracket, `H(t_k)` for the free motion plus the constant share, `P^u(t_k)` for the constant
share, and the `Ũ`-input's share in the sum `P̂^U_0(t_k) + P̂^U_∞(t_k)` of the two halves of
eq. (27), kept apart.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real SoundFloatArithmetic Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state `s` of a run from `X₀` under inputs in `V` holds what it owes at `t_k`. -/
def LinearSys.AutoInvariantFloat (sys : LinearSys 𝕋 n) (X₀ V : Float.Zonotope (Vec 𝕋 n))
    (s : LinearSys.AutoStateFloat 𝕋 n) : Prop :=
  0 ≤ s.t ∧ toReal s.tLo ≤ (s.t : ℝ) ∧ (s.t : ℝ) ≤ toReal s.tHi ∧
    (∀ x ∈ X₀.construct, exp ((s.t : ℝ) • Scalar.toRealMat sys.A) *ᵥ x
      + MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recenter.center V ∈ s.H.construct) ∧
    MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recenter.center V ∈ s.Pu.construct ∧
    ∀ y ∈ sys.inputReach (S := 𝒵[𝕋]) (Recenter.recenter V) s.t,
      y ∈ s.PU0.construct + s.PUinf.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

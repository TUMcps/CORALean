import CORALean.ContDynamics.LinearSys.Definitions.AutoStateFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# What an `Alg. 2` state owes at `t_k`, in floats

`AutoInvariantFloat`: the state of a run from `X₀` under inputs in `V` holds, at `t_k`, the time
bracket, `H(t_k)` for the free motion plus the constant share, `P^u(t_k)` for the constant
share, and the `Ũ`-input's share in the sum `P̂^U_0(t_k) + P̂^U_∞(t_k)` of the two halves of
eq. (27), kept apart.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real SoundFloatArithmetic Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state `s` of a run from `X₀` under inputs in `V` holds what it owes at `t_k`. -/
def LinearSys.AutoInvariantFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope 𝕋 n)
    (s : LinearSys.AutoStateFloat 𝕋 n) : Prop :=
  0 ≤ s.t ∧ toReal s.tLo ≤ (s.t : ℝ) ∧ (s.t : ℝ) ≤ toReal s.tHi ∧
    (∀ x ∈ X₀.construct, exp ((s.t : ℝ) • Scalar.toRealMat sys.A) *ᵥ x
      + MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recentre.centre V ∈ s.H.construct) ∧
    MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recentre.centre V ∈ s.Pu.construct ∧
    ∀ y ∈ sys.inputReach (S := Zonotope 𝕋) (Recentre.recentre V) s.t,
      y ∈ s.PU0.construct + s.PUinf.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

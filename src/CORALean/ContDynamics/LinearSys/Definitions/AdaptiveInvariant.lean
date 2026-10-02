import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveState
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# What the state of an adaptive float run owes

With the input set `V` split `ũ ⊕ Ũ` at its stored centre: `t_i` is
nonnegative and inside its float bracket, and `P` holds the constant's
contribution by `t_i` plus anything an admissible `Ũ`-input contributes by
then. The free motion is not carried: [1, Alg. 1] reaches every window from
`X₀` by `e^{A t_i}`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state `s` of a run under inputs in `V` holds what it owes at `t_i`. -/
def LinearSys.AdaptiveInvariant (sys : LinearSys 𝕋 n) (V : Zonotope 𝕋 n)
    (s : LinearSys.AdaptiveState 𝕋 n) : Prop :=
  0 ≤ s.t ∧ toReal s.tLo ≤ (s.t : ℝ) ∧ (s.t : ℝ) ≤ toReal s.tHi ∧
    ∀ y ∈ sys.inputReach (S := Zonotope 𝕋) (Recentre.recentre V) s.t,
      MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recentre.centre V + y ∈ s.P.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

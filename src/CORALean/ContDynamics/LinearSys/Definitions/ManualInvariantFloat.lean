module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# What the state of a float run of `Alg. 1` owes

With the input set `V` split `ũ ⊕ Ũ` at its stored centre, as [1, Alg. 1] line 1 splits it:
`t_k` is nonnegative and inside its float bracket, `H` holds the free motion plus the
constant's share `P^u(t_k)` from every initial state, `Pu` holds `P^u(t_k)`, and `PU` holds
anything an admissible `Ũ`-input contributes by `t_k`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state `s` of a run from `X₀` under inputs in `V` holds what it owes at `t_k`. -/
def LinearSys.ManualInvariantFloat (sys : LinearSys 𝕋 n) (X₀ V : Float.Zonotope (Vec 𝕋 n))
    (s : LinearSys.ManualStateFloat 𝕋 n) : Prop :=
  0 ≤ s.t ∧ toReal s.tLo ≤ (s.t : ℝ) ∧ (s.t : ℝ) ≤ toReal s.tHi ∧
    (∀ x ∈ X₀.construct, exp ((s.t : ℝ) • Scalar.toRealMat sys.A) *ᵥ x
      + MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recentre.centre V ∈ s.H.construct) ∧
    MatExp.expIntegral (Scalar.toRealMat sys.A) s.t *ᵥ Recentre.centre V ∈ s.Pu.construct ∧
    ∀ y ∈ sys.inputReach (S := fun k => Float.Zonotope (Vec 𝕋 k)) (Recentre.recentre V) s.t, y ∈
      s.PU.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

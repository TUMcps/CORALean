import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# What the state of `reachFloatInput`'s loop holds after `k` passes

With the input split `ũ ⊕ Ũ`: `H(t_{k+1})` holds the free motion and the
constant's contribution at `t_{k+1}`, `H(τ_k)` the same at every time of window
`k`, `P^R(t_{k+1})` everything an admissible `Ũ`-input contributes by
`t_{k+1}`, and the propagated one-step set the one-step contributions carried
across `t_k`. The four sets the loop's state names, and what each must enclose.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The four enclosures the loop state `s` owes after `k` passes, steps `Δt`,
initial states `X₀`, constant input `ũ` and recentred input set `Ũ`. -/
def LinearSys.ReachFloatInputInvariant (sys : LinearSys 𝕋 n) (Δt : ℝ) (X₀ : Set (Vec ℝ n))
    (ũ : Vec ℝ n) (Ũ : Float.Zonotope (Vec 𝕋 n)) (k : ℕ)
    (s : Float.Zonotope (Vec 𝕋 n) × Float.Zonotope (Vec 𝕋 n) × Float.Zonotope (Vec 𝕋 n) ×
    Float.Zonotope (Vec 𝕋 n)) : Prop :=
  let A := Scalar.toRealMat sys.A
  (∀ x₀ ∈ X₀, exp ((((k + 1 : ℕ) : ℝ) * Δt) • A) *ᵥ x₀
      + MatExp.expIntegral A (((k + 1 : ℕ) : ℝ) * Δt) *ᵥ ũ ∈ s.1.construct) ∧
    (∀ x₀ ∈ X₀, ∀ τ ∈ Set.Icc 0 Δt, exp (((k : ℝ) * Δt + τ) • A) *ᵥ x₀
      + MatExp.expIntegral A ((k : ℝ) * Δt + τ) *ᵥ ũ ∈ s.2.1.construct) ∧
    sys.inputReach (S := fun k => Float.Zonotope (Vec 𝕋 k)) Ũ (((k + 1 : ℕ) : ℝ) * Δt) ⊆
      s.2.2.1.construct ∧
    (fun y => exp (((k : ℝ) * Δt) • A) *ᵥ y) '' sys.inputReach
      (S := fun k => Float.Zonotope (Vec 𝕋 k)) Ũ Δt
      ⊆ s.2.2.2.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoGenSet
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# What the zonotope verification pass keeps true at `t_k`

The state of `LinearSys.verifyZonotopePassFloat` at time `t` encloses the system
`ẋ = Ax + u₀ + v`, `v(t) ∈ V`, from `X₀ = ⟨c₀, G₀⟩`, with the scales `s`:
* every `e^{tA}(c₀ + G₀ b) + (∫₀ᵗ e^{σA} dσ) u₀` is within `h sᵢ` of `c + G b`, entry by entry, for
  the same `b ∈ [-1, 1]^m`;
* `e^{tA} - Φ` maps every `x` with `|x_k| ≤ a s_k` into `|·ᵢ| ≤ φ a sᵢ`;
* every point the varying input reaches by `t` is spanned by `P` plus a point of the box `b` plus
  one within `ρ sᵢ`;
and the time and the three error bounds are nonnegative.

## Inputs
* `sys` – linear system
* `s` – positive scales
* `c₀` – center of the initial set
* `G₀` – generators of the initial set
* `u₀` – constant input
* `V` – set of the varying input
* `t` – time
* `st` – float state of the pass

## Output
* whether the state encloses the system at `t`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state `st` encloses the system at `t`: the carried zonotope, `e^{tA}`, the varying input. -/
def LinearSys.IsVerifyZonoInvariant (sys : LinearSys 𝕋 n) (s : Vec ℝ n) (c₀ : Vec ℝ n)
    (G₀ : Mat ℝ n m) (u₀ : Vec ℝ n) (V : Set (Vec ℝ n)) (t : ℝ)
    (st : LinearSys.VerifyZonoState 𝕋 n m) : Prop :=
  0 ≤ t ∧ 0 ≤ toReal st.h ∧ 0 ≤ toReal st.φ ∧ 0 ≤ toReal st.ρ ∧
  (∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ i,
    |(exp (t • toRealMat sys.A) *ᵥ (c₀ + G₀ *ᵥ b)
      + Real.MatExp.expIntegral (toRealMat sys.A) t *ᵥ u₀
      - (toRealVec st.c + toRealMat st.G *ᵥ b)) i| ≤ toReal st.h * s i) ∧
  (∀ a : ℝ, 0 ≤ a → ∀ x : Vec ℝ n, (∀ k, |x k| ≤ a * s k) → ∀ i,
    |((exp (t • toRealMat sys.A) - toRealMat st.Φ) *ᵥ x) i| ≤ toReal st.φ * a * s i) ∧
  ∀ y ∈ sys.inputReach (S := ExactSet) V t, ∃ y' ∈ LinearSys.verifyZonoGenSet (st.P.map toRealVec),
    ∃ e₁ e₂ : Vec ℝ n, (∀ i, |e₁ i| ≤ toReal (st.b i)) ∧ (∀ i, |e₂ i| ≤ toReal st.ρ * s i) ∧
      y = y' + e₁ + e₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

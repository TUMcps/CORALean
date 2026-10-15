module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagateFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat

@[expose] public section

/-!
# One window with the input set split, at every member, in floats

`LinParamSys.reachStepkInput` computed in `𝕋`, `V = ũ ⊕ Ũ` the input set of the state space
split at its stored center [1, Alg. 4]:
`R(τ_k) = [e^{[A]t_k}](H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`. The first
window's set `Rτ₀ = (H^R ⊕ P̃^R)(τ_0)` is taken, as `reachStepkFloat` takes `H^R(τ_0)`,
so no window pays for it again.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, the input set `V` of the
state space split at its center, at every member of `sys.A`. -/
def LinParamSys.reachStepkFloatInput
    (sys : LinParamSys ℐ[𝕋] n) (V : Zonotope (Vec 𝕋 n)) (ρ : ℕ)
    (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope (Vec 𝕋 n)) (k : ℕ) : Option (Zonotope (Vec 𝕋 n)) := do
  let uc := ScalarCenter.centerVec (S := 𝒵[𝕋]) V           -- ũ, the constant
  let U₀ := Recenter.recenter V                                    -- Ũ = V - ũ, holding 0
  let Hτk ← sys.reachStepkFloat Δt η Rτ₀ k                         -- [e^{[A]t_k}](H^R ⊕ P̃^R)(τ_0)
  let Pctk := sys.constPropagateFloat Δt η ρ uc k                  -- P̃(t_k)
  let PRtk ← sys.particularSolutionFloat Δt η ρ U₀ k               -- P^R_Ũ(t_{k+1})
  pure ((Hτk ⊞ Pctk) ⊞ PRtk)                                       -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

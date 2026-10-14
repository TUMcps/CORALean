module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
public import CORALean.ContDynamics.LinearSys.Operations.SampleTimeFloat
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# One window at every member, in floats: `H^R(τ_k) = [e^{[A] t_k}] H^R(τ_0)`

`LinParamSys.reachStepk` computed in `𝕋`, the window's matrix enclosed afresh at
`t_k` as `LinearSys.reachStepkWrappingFreeFloat` encloses it at a point:
`sampleTimeFloat` brackets `t_k`, and `expSquaringFloat` encloses `e^{At}` over
that bracket at every member, with `s ≈ log₂ k` squarings from `squaringsFloat`,
so the step's order `η` serves every window. No window when no `s` is found.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, at every member,
the exponential at order `η` after scaling `t_k` down to the step. -/
def LinParamSys.reachStepkFloat (sys : LinParamSys ℐ[𝕋] n)
    (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope (Vec 𝕋 n)) (k : ℕ) : Option (Zonotope (Vec 𝕋 n)) := do
  let tk := LinearSys.sampleTimeFloat Δt k                          -- [t_k], bracketed
  let sk ← sys.squaringsFloat Δt tk.inf tk.sup η                        -- t_k / 2^s within Δt
  let eAtk := sys.expSquaringFloat tk.inf tk.sup η sk                   -- [e^{[A] t_k}], squared
  pure (Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- H^R(τ_k)
    (S := 𝒵[𝕋]) eAtk Rτ₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

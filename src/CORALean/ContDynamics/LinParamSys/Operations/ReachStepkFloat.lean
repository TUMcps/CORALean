import CORALean.ContDynamics.LinParamSys.Operations.ExpSquaringFloat
import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
import CORALean.ContDynamics.LinearSys.Operations.SampleTimeFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One window at every member, in floats: `H^R(τ_k) = [e^{[A] t_k}] H^R(τ_0)`

`LinParamSys.reachStepk` computed in `𝕋`, the window's matrix enclosed afresh at
`t_k` as `LinearSys.reachStepkWrappingFreeFloat` encloses it at a point:
`sampleTimeFloat` brackets `t_k`, and `expSquaringFloat` encloses `e^{At}` over
that bracket at every member, with `s ≈ log₂ k` squarings from `squaringsFloat`,
so the step's order `η` serves every window. No window when no `s` is found.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, at every member,
the exponential at order `η` after scaling `t_k` down to the step. -/
def LinParamSys.reachStepkFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope 𝕋 n) (k : ℕ) : Option (Zonotope 𝕋 n) := do
  let tk := LinearSys.sampleTimeFloat Δt k                          -- [t_k], bracketed
  let sk ← sys.squaringsFloat Δt tk.1 tk.2 η                        -- t_k / 2^s within Δt
  let eAtk := sys.expSquaringFloat tk.1 tk.2 η sk                   -- [e^{[A] t_k}], squared
  pure (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAtk Rτ₀)  -- H^R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

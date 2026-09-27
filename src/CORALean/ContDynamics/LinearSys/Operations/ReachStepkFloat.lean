import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
import CORALean.ContDynamics.LinearSys.Operations.SampleTimeFloat
import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One window of `reachFloat`: `R(τ_k) = [e^{A t_k}] R(τ_0)`, in floats

`reachStepk` computed in `𝕋`. The matrix is enclosed afresh at `t_k` itself,
never as a power of `[e^{AΔt}]`, so no window pays for the ones before it. A
float need not hold `t_k = k Δt`, so the window brackets it, `sampleTimeFloat`,
and encloses `e^{At}` over that whole range: sound at every float `Δt`. The
enclosure is scaling and squaring, `expSquaringFloat`, with `s ≈ log₂ k`
squarings from `squaringsFloat`: the scaled range is as short as the step, so
the step's order `η` serves every window, and the chain is `s` products of one
fresh matrix — rounding compounds `O(s)` times per window, not `O(k)`. No window
when no `s` is found.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, the
exponential at order `η` after scaling `t_k` down to the step. -/
def LinearSys.reachStepkFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope 𝕋 n)
    (k : ℕ) : Option (Zonotope 𝕋 n) := do
  let tk := LinearSys.sampleTimeFloat Δt k                          -- [t_k], bracketed
  let sk ← sys.squaringsFloat Δt tk.1 tk.2 η                        -- t_k / 2^s within Δt
  let eAtk := sys.expSquaringFloat tk.1 tk.2 η sk                   -- [e^{A t_k}], squared
  pure (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAtk Rτ₀)  -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

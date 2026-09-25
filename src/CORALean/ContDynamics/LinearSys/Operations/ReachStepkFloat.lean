import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.WindowOrderFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# One window of `reachFloat`: `R(τ_k) = [e^{A t_k}] R(τ_0)`, in floats

`reachStepk` computed in `𝕋`. The matrix is enclosed afresh at `t_k` itself,
never as a power of `[e^{AΔt}]`, so no window pays for the ones before it. A
float need not hold `t_k = k Δt`, so the window brackets it by the two sums of
`k` copies of `Δt`, one rounded down and one up, and encloses `e^{At}` over that
whole range: sound at every float `Δt`. `‖A t_k‖` grows with `k`, so each window
raises the order again with `windowOrderFloat` until the enclosure is as tight as
the step's, and has no window when that search finds no order.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, at an order
raised from `η` until as accurate at `t_k` as the step is at order `η`. -/
def LinearSys.reachStepkFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope 𝕋 n)
    (k : ℕ) : Option (Zonotope 𝕋 n) := do
  let tLo := nsmulDown k Δt                                          -- t_k, rounded down
  let tHi := nsmulUp k Δt                                            -- t_k, rounded up
  let ηk ← sys.windowOrderFloat Δt tLo tHi η                        -- as accurate as the step
  let eAtk := sys.expIntervalFloat tLo tHi ηk                       -- [e^{A t_k}]
  pure (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAtk Rτ₀)  -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

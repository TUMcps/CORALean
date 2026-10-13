import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContDynamics.Reach.Operations.Steps
import CORALean.Global.Float.ToRat

/-!
# The time-point sets of `reachWrappingFreeFloat`'s scheme: `R_k = [e^{A t_k}] X₀`

`reachWrappingFreeFloat` returns only its time-interval windows; the time-point set at
`t_k = k Δt` is the same enclosure `reachStepkWrappingFreeFloat` builds from `R(τ_0)`,
here applied to `X₀` itself instead — `reachStepkWrappingFreeFloat` asks nothing of its
base zonotope beyond membership, so no new window logic is needed, only the
order search redone once as `reachWrappingFreeFloat` redoes it, `N` derived as it
derives it. `N + 1` points, `k = 0, …,
N`; `k = 0` gives (an enclosure of) `X₀` itself, `e^{A · 0} = I`. `params` and
`options` are read as `reachWrappingFreeFloat` reads them; no set is reduced, so
`zonotopeOrder` goes unread.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-point sets `R_0, …, R_N` from `X₀`, at Taylor order `η` raised
until admissible, each window `[e^{A t_k}] X₀` computed directly from `X₀`. -/
def LinearSys.reachTimePointWrappingFreeFloat (sys : LinearSys 𝕋 n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ) (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let η := options.taylorTerms
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  (List.range (N + 1)).mapM (sys.reachStepkWrappingFreeFloat Δt η' X₀)       -- R_k = [e^{A t_k}] X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

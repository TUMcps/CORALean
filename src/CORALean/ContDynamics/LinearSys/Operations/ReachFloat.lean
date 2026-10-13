import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContDynamics.Reach.Operations.Steps
import CORALean.Global.Float.ToRat

/-!
# Recursive reachability in floats: `R_{k+1} = reduce([e^{AΔt}] R_k, ρ)`

[1, Alg. 4] at a point matrix, no input, in `𝕋` — CORA's `linAlg = 'standard'`,
`X₀ = params.R0`, `Δt`, `η`, `ρ` the `options`' `timeStep`, `taylorTerms`,
`zonotopeOrder`, `N = (tFinal - tStart) / Δt` by `Reach.steps`, `none` unless a
natural number: time-point sets `R_0 = X₀, …, R_N` by `timePointStepFloat` and
Girard's reduction to order `ρ`, window `k < N` by `timeIntervalStepFloat` from
`R_k`, not reduced; nothing is propagated from it.

The error box is never folded into a generator: `mtimesIntervalMat` multiplies
it by the interval matrix every step, its width going to `n` new generators as
in CORA, and `reduce` keeps it, Girard's box becoming `n` generators. So the box
holds rounding alone and wraps — it grows with the matrix's norm, step after
step — the effect `reachWrappingFreeFloat` avoids; the generators stay at order `ρ`.

The two matrices are computed once, `η` raised as `reachWrappingFreeFloat` raises it, and
the steps apply them in place: `timePointStepFloat` and `timeIntervalStepFloat`
compute them per call, which the compiler does not share across calls.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `R(τ_0), …, R(τ_{N-1})` and the time-point sets `R_0, …, R_N`
from `X₀`, reducing to order `ρ` after every step. -/
def LinearSys.reachFloat (sys : LinearSys 𝕋 n) (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n)) × List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let η := options.taylorTerms
  let ρ := options.zonotopeOrder
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let eAΔt := sys.expIntervalFloat Δt Δt η'                         -- [e^{AΔt}], once
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F], once
  let next := fun R =>                                              -- reduce([e^{AΔt}] R_k, ρ)
    Reduce.reduce (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt R) ρ
  let Rtp := List.iterate next X₀ (N + 1)                           -- R_0, …, R_N
  let Rti := (Rtp.take N).map fun R =>                              -- R(τ_k) from R_k
    LinComb.linComb R (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt R) ⊞
      Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k)) F R
  pure (Rti, Rtp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat

/-!
# Recursive reachability in floats: `R_{k+1} = reduce([e^{AΔt}] R_k, ρ)`

[1, Alg. 4] at a point matrix and without an input, computed in `𝕋`: the
time-point sets `R_0 = X₀, …, R_N` by `timePointStepFloat` and Girard's
reduction to order `ρ`, and window `k < N` by `timeIntervalStepFloat` from
`R_k`. The windows are not reduced; nothing is propagated from them.

The error box is never folded into a generator: `mtimesIntervalMat` multiplies
it by the interval matrix every step, the matrix's own width going to `n` new
generators as in CORA, and `reduce` keeps it as it is, Girard's box of the
dropped generators becoming `n` generators. So the box holds rounding alone and
wraps — it grows with the matrix's norm, step after step — which is the effect
`reachFloat` avoids; the generators, `n` more per step, stay at order `ρ`.

The two matrices are computed once, `η` raised as `reachFloat` raises it, and
the steps apply them in place: `timePointStepFloat` and `timeIntervalStepFloat`
compute them per call, which the compiler does not share across calls.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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

/-- The windows `R(τ_0), …, R(τ_{N-1})` and the time-point sets `R_0, …, R_N`
from `X₀`, reducing to order `ρ` after every step. -/
def LinearSys.reachRecursiveFloat (sys : LinearSys 𝕋 n) (X₀ : Zonotope 𝕋 n) (Δt : 𝕋)
    (η ρ N : ℕ) : Option (List (Zonotope 𝕋 n) × List (Zonotope 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let eAΔt := sys.expIntervalFloat Δt Δt η'                         -- [e^{AΔt}], once
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F], once
  let next := fun R =>                                              -- reduce([e^{AΔt}] R_k, ρ)
    Reduce.reduce (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt R) ρ
  let Rtp := List.iterate next X₀ (N + 1)                           -- R_0, …, R_N
  let Rti := (Rtp.take N).map fun R =>                              -- R(τ_k) from R_k
    LinComb.linComb R (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt R) ⊞
      Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) F R
  pure (Rti, Rtp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

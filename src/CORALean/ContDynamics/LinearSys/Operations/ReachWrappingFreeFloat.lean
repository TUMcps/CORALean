import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat

/-!
# Wrapping-free reachability in floats: `R(τ_k) = [e^{A t_k}] R(τ_0)`

[1, Alg. 1] without an input, computed in `𝕋`: the first window is
`timeIntervalStepFloat`, reduced by Girard's rule to order `ρ` (`ρ` at or above
its order leaves it alone), and window `k < N` is that one set carried by an
enclosure of `e^{A t_k}` taken at `t_k` directly — `reachStepkWrappingFreeFloat` — so no
window's error compounds into the next one's.

`η` is raised with `reachOrderFloat` to the first order from `max η 2` the float
remainder bound at `Δt · A` admits; each window scales `t_k` down to the step
by squarings and keeps that order. `none` when a search fails; otherwise `N`
windows.

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

/-- The windows `τ_0, …, τ_{N-1}` of width `Δt` from `X₀`, the first reduced to
order `ρ`, at Taylor order `η` raised until admissible. -/
def LinearSys.reachWrappingFreeFloat (sys : LinearSys 𝕋 n) (X₀ : Zonotope 𝕋 n) (Δt : 𝕋)
    (η ρ N : ℕ) : Option (List (Zonotope 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let Rτ₀ := Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀) ρ   -- R(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkWrappingFreeFloat Δt η' Rτ₀)     -- R(τ_k) = [e^{A t_k}] R(τ_0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

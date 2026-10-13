import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.Reach.Definitions.InputParams
import CORALean.ContDynamics.Reach.Operations.Steps
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.Global.Float.ToRat

/-!
# Wrapping-free reachability with inputs in floats

`ẋ = Ax + Bu`, `u(t) ∈ U` arbitrary in time, in `𝕋`, read and split as
`reachFloatInput` reads and splits it, with windows taken as
`reachWrappingFreeFloat` takes them: [1, Alg. 3]'s window
`R(τ_k) = e^{A t_k}(H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R(t_{k+1})`, as
`WithInputSplit.reachStepk` states it over ℝ, with `[e^{A t_k}]` taken at `t_k`
directly (`reachStepkWrappingFreeFloat`), so no window's error compounds into the
next. `P^R(t_{k+1}) = e^{A t_k} P^R(Δt) ⊕ P^R(t_k)`, so the first summand is
carried with the first window and the rest accumulates from `{0}` by
`P(t_{k+1}) = P(t_k) ⊕ [e^{A t_k}](P̃(Δt) ⊕ P^R(Δt))`, reduced to order `ρ`.
CORA's `priv_reach_wrappingfree` steps by `[e^{AΔt}]` and keeps the input in a
box instead; the float layer's choice is `reachWrappingFreeFloat`'s.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of `ẋ = Ax + Bu` from `X₀` under inputs in
`U`, each from the first by `[e^{A t_k}]`, the accumulated input reduced to `ρ`. -/
def LinearSys.reachWrappingFreeFloatInput (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let η := options.taylorTerms
  let ρ := options.zonotopeOrder
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := Mtimes.mtimes (𝕄 := Mat 𝕋)  -- B U, in the state space
    (S := fun k => Zonotope (Vec 𝕋 k)) B params.U
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored centre
  let Ũ := Recentre.recentre V                                      -- Ũ = V - ũ, holding 0
  let O := (Interval.point fun _ => zero).zonotope                  -- {0}
  let Pu := sys.inputSolutionFloat Δt η' ũ                          -- P̃(Δt)
  let PuR := sys.inputSolutionFloat Δt η' (LinComb.linComb O ũ)     -- P̃^R(τ_0), from [0, ũ]
  let PU := sys.inputSolutionFloat Δt η' Ũ                          -- P^R(Δt)
  let Rτ₀ := Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀ ⊞ PuR) ρ   -- (H^R ⊕ P̃^R)(τ_0)
  let Hτ ← (List.range N).mapM                                      -- [e^{A t_k}](Rτ₀ ⊕ P^R(Δt))
    (sys.reachStepkWrappingFreeFloat Δt η' (Rτ₀ ⊞ PU))
  let Pτ ← (List.range N).mapM                                      -- [e^{A t_k}](P̃ ⊕ P^R)(Δt)
    (sys.reachStepkWrappingFreeFloat Δt η' (Pu ⊞ PU))
  let P := Pτ.scanl (fun P Q => Reduce.reduce (P ⊞ Q) ρ) O          -- P̃(t_k) ⊕ P^R(t_k)
  pure (List.zipWith (· ⊞ ·) Hτ P)                                  -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

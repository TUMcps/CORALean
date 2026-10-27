module

public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# Wrapping-free reachability with inputs in floats

`ẋ = Ax + Bu + c`, `u(t) ∈ U` arbitrary in time, in `𝕋`, read and split as `reachFloatInput` reads
and splits it, with windows taken as `reachWrappingFreeFloat` takes them: the window
`R(τ_k) = e^{A t_k}(H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R(t_{k+1})`, [1, Eq. 4]'s split-input step
at the first window carried to `τ_k` (`WithInputSplit.reachStepk` over ℝ), `[e^{A t_k}]` taken at
`t_k` directly, so no window's error compounds into the next.
`P^R(t_{k+1}) = e^{A t_k} P^R(Δt) ⊕ P^R(t_k)`, so the first summand is carried with the first window
and the rest accumulates from `{0}` by `P(t_{k+1}) = P(t_k) ⊕ [e^{A t_k}](P̃(Δt) ⊕ P^R(Δt))`,
reduced to order `ρ`. CORA's `priv_reach_wrappingfree` steps by `[e^{AΔt}]` and boxes the input.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Output
* float windows of the run with inputs, if it completes

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of `ẋ = Ax + Bu + c` from `X₀` under inputs in
`U`, each from the first by `[e^{A t_k}]`, the accumulated input reduced to `ρ`. -/
def LinearSys.reachWrappingFreeFloatInput (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := sys.inputSetFloat params.U                               -- B U ⊕ c, in the state space
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let O := (Interval.point fun _ => zero).zonotope                  -- {0}
  let Pu := sys.inputSolutionFloat Δt η' ũ                          -- P̃(Δt)
  let PuR := sys.inputSolutionFloat Δt η' (LinComb.linComb O ũ)     -- P̃^R(τ_0), from [0, ũ]
  let PU := sys.inputSolutionFloat Δt η' Ũ                          -- P^R(Δt)
  let Rτ₀ := Reduce.reduce (sys.timeIntervalFloat Δt η' X₀ ⊞ PuR) ρ   -- (H^R ⊕ P̃^R)(τ_0)
  let Hτ ← (List.range N).mapM                                      -- [e^{A t_k}](Rτ₀ ⊕ P^R(Δt))
    (sys.reachStepkWrappingFreeFloat Δt η' (Rτ₀ ⊞ PU))
  let Pτ ← (List.range N).mapM                                      -- [e^{A t_k}](P̃ ⊕ P^R)(Δt)
    (sys.reachStepkWrappingFreeFloat Δt η' (Pu ⊞ PU))
  let P := Pτ.scanl (fun P Q => Reduce.reduce (P ⊞ Q) ρ) O          -- P̃(t_k) ⊕ P^R(t_k)
  pure (List.zipWith (· ⊞ ·) Hτ P)                                  -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

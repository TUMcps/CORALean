module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloatInput

@[expose] public section

/-!
# Reachability with inputs of a set-valued-matrix system in floats

`LinParamSys.WithInput.reachUnion` computed in `𝕋`, `0 ∈ U`, as [1, Alg. 4] reads at a
constant parameter: `reachFloat`'s windows, each with the input's contribution
`particularSolutionFloat` added by `reachStepkFloatInput`. `none` when the order,
a window's squaring count or the accumulation fails.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of width `Δt` from `X₀` at every member of `sys.A`,
under inputs in `U`, the first reduced to order `ρ`, at Taylor order `η` raised
until admissible. -/
def LinParamSys.reachFloatInput (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (U : Zonotope (Vec 𝕋 n)) (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let HRτ₀ := Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀) ρ  -- H^R(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkFloatInput U ρ Δt η' HRτ₀)     -- R(τ_k), every k < N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

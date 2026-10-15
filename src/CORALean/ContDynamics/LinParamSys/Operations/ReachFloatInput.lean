module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloatInput

@[expose] public section

/-!
# Reachability with inputs of a set-valued-matrix system in floats

`LinParamSys.reachUnion` computed in `𝕋`, the input set `params.U` in input coordinates anywhere,
[1, Alg. 4]: `V = B U` is formed here, as `LinearSys.reachFloatInput` forms `B U ⊕ c`, and
taken apart at its centre, `ũ` carried across windows by `constPropagateFloat` and the rest,
holding the origin, by `particularSolutionFloat`, window by window as `reachStepkFloatInput` has
it. The offset `sys.c` is a real vector, which no float run can add: it is left out, and
`reachFloatInput_outer` asks it to be `0`. `none` when the order, a window's squaring count or
the accumulation fails.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of width `Δt` from `X₀` at every member of `sys.A`, under
inputs `params.U` in input coordinates wherever they sit, the first reduced to order `ρ`, at
Taylor order `η` raised until admissible. -/
def LinParamSys.reachFloatInput (sys : LinParamSys ℐ[𝕋] n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) sys.B params.U    -- V = B U, in the state space
  let uc := ScalarCentre.centreVec (S := 𝒵[𝕋]) V                    -- ũ, the constant
  let HRτ₀ := sys.timeIntervalStepFloat Δt η' X₀                    -- H^R(τ_0)
  let PcRτ₀ := sys.constInputSolutionFloat Δt η' uc                 -- P̃^R(τ_0), ũ over τ_0
  let Rτ₀ := Reduce.reduce (HRτ₀ ⊞ PcRτ₀) ρ                         -- (H^R ⊕ P̃^R)(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkFloatInput V ρ Δt η' Rτ₀)      -- R(τ_k), every k < N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

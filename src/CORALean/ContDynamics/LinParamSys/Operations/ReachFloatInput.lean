module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloatInput
public import CORALean.ContSet.Zonotope.Float.Operations.Point

@[expose] public section

/-!
# Reachability with inputs of a set-valued-matrix system in floats

`LinParamSys.reachUnion` computed in `𝕋`, the input set `params.U` in input coordinates anywhere,
[1, Alg. 1]: `V = B U ⊕ c` is formed here, as `LinearSys.reachFloatInput` forms it, and
taken apart at its center, `ũ` carried across windows by `constPropagateFloat` and the rest,
holding the origin, by `particularSolutionFloat`, window by window as `reachStepkFloatInput` has
it. The offset `sys.c` is a real vector, which no float run can add, so the run takes the float
vector `c` that stands for it, as `LinearSys 𝕋 n` stores its `c` in `𝕋`; `reachFloatInput_outer`
relates it to the system's through `toRealVec`. `none` when the order, a window's squaring count
or the accumulation fails.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
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
Taylor order `η` raised until admissible; `c` is the offset `sys.c` in `𝕋`. -/
def LinParamSys.reachFloatInput (sys : LinParamSys ℐ[𝕋] n) (c : Vec 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) sys.B params.U    -- V = B U ⊕ c, in the
    ⊞ Zonotope.point c                                              -- state space
  let uc := ScalarCenter.centerVec (S := 𝒵[𝕋]) V                    -- ũ, the constant
  let HRτ₀ := sys.timeIntervalStepFloat Δt η' X₀                    -- H^R(τ_0)
  let PcRτ₀ := sys.constInputSolutionFloat Δt η' uc                 -- P̃^R(τ_0), ũ over τ_0
  let Rτ₀ := Reduce.reduce (HRτ₀ ⊞ PcRτ₀) ρ                         -- (H^R ⊕ P̃^R)(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkFloatInput V ρ Δt η' Rτ₀)      -- R(τ_k), every k < N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

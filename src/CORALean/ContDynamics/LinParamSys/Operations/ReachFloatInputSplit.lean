module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloatInputSplit

@[expose] public section

/-!
# Reachability with the input set split, of a set-valued-matrix system in floats

`LinParamSys.WithInputSplit.reachUnion` computed in `𝕋`, the input set anywhere, [1, Alg. 4]: `U` is
taken apart at its centre, `ũ` carried across windows by `constPropagateFloat` and the
rest, holding the origin, by `particularSolutionFloat`, window by window as
`reachStepkFloatInputSplit` has it. `none` when the order, a window's squaring count or
the accumulation fails.

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
under inputs in `U` wherever it sits, the first reduced to order `ρ`, at Taylor order
`η` raised until admissible. -/
def LinParamSys.reachFloatInputSplit (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (U : Zonotope (Vec 𝕋 n)) (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let uc := ScalarCentre.centreVec (S := fun k => Zonotope (Vec 𝕋 k)) U  -- ũ, the constant
  let HRτ₀ := sys.timeIntervalStepFloat Δt η' X₀                    -- H^R(τ_0)
  let PcRτ₀ := sys.constInputSolutionFloat Δt η' uc                 -- P̃^R(τ_0), ũ over τ_0
  let Rτ₀ := Reduce.reduce (HRτ₀ ⊞ PcRτ₀) ρ                         -- (H^R ⊕ P̃^R)(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkFloatInputSplit U ρ Δt η' Rτ₀) -- R(τ_k), every k < N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

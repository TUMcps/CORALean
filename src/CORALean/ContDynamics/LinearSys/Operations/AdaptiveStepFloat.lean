module

public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveOptions
public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveState
public import CORALean.ContDynamics.LinearSys.Definitions.AdaptiveStepInfo
public import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.AdaptSetOrder
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Alg. 1` lines 5-10 in floats: one iteration of the main loop

`aux_tunedStep` computed in `𝕋`, with `V` split `ũ ⊕ Ũ` at its stored center:
`Alg. 2` picks `Δt_i` and `Φ_prop,i`, eq. (2) carries the solutions from
`[0,Δt_i]` to `[t_i,t_{i+1}]` by `[e^{At_i}]`, `Alg. 3` reduces the input's
accumulated share, and `R([t_i,t_{i+1}])` is their sum. What the tuning picks
is a candidate only: the step must be positive and `Φ_prop,i` admissible for
the float enclosures, both decided exactly in ℚ, and every set is a sound
float step. `toRat` reads a NaN as the number `1.5 · 2 ^ 1024`, so the step and the norm
bound `nrm` are also refused if `isNaN`.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `t₀` – start time
* `tf` – final time
* `options` – adaptive options
* `s` – loop state

## Output
* report of the step and the next state, if the step succeeds

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-10: one iteration of [1, Alg. 1] from `X₀` under inputs in `V`, horizon
`tf` after `t₀`: the step's report and the next state, or `none`. -/
def LinearSys.adaptiveStepFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (t₀ tf : ℚ)
    (options : LinearSys.AdaptiveOptions 𝕋) (s : LinearSys.AdaptiveState 𝕋 n) :
    Option (LinearSys.AdaptiveStepInfo 𝕋 n × LinearSys.AdaptiveState 𝕋 n) := do
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let ηe := max options.ηmax 2                                      -- [e^{At_i}]'s order
  let sq ← sys.squaringsFloat s.Δt s.tEnc.inf s.tEnc.sup ηe        -- t_i / 2^sq within Δt_{i-1}
  let eAt := sys.expSquaringFloat s.tEnc.inf s.tEnc.sup ηe sq                 -- [e^{A t_i}]
  let eA := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{A t_i}] ·
    (S := 𝒵[𝕋]) eAt
  -- 5. Alg. 2
  let (Δt, η, εH, εP) ← sys.adaptTimeStepFloat eAt X₀ Ũ options.εHmax
    options.εPmax s.εP tf s.t s.Δt options.μ options.ηmax options.fuel
  let nrm := MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A))  -- ≥ ‖Δt A‖
  if 0 < ToRat.toRat Δt ∧ 2 ≤ η ∧ ToRat.toRat nrm / ((η : ℚ) + 2) ≤ 1 / 2  -- admissible
      ∧ ToRat.isNaN Δt = false ∧ ToRat.isNaN nrm = false then              -- not read from a NaN
    -- 6. HR([0,Δt_i])
    let HR₀ := sys.timeIntervalFloat Δt η X₀
    let PuR := sys.inputSolutionFloat Δt η seg                      -- P̃^R([0,Δt_i]), from [0, ũ]
    let Pu := sys.inputSolutionFloat Δt η ũ                         -- P̃(Δt_i)
    -- 6. PR([0,Δt_i])
    let PU := sys.inputSolutionFloat Δt η Ũ
    -- 7. e^{At_i}(HR ⊕ PR)
    let HR := eA (HR₀ ⊞ PuR ⊞ PU)
    -- 7. (P̃ ⊕ PR)(t_{i+1})
    let PR := s.P ⊞ eA (Pu ⊞ PU)
    -- 8. Alg. 3
    let (Φset, εS) := Zonotope.adaptSetOrder PR options.εSmax s.εS tf s.t Δt
    -- 8. red(PR, Φ_set,i)
    let PRred := Reduce.reduce PR Φset
    -- 9. R([t_i,t_{i+1}])
    let R := HR ⊞ s.P
    -- 10. t ← t + Δt_i
    let t' := s.t + ToRat.toRat Δt
    some ({ tStart := t₀ + s.t, tEnd := t₀ + min t' tf, Δt := Δt, η := η,
            ρ := Φset, R := R, εH := εH, εP := εP, εS := εS },
          { t := t', tEnc := ⟨addDown s.tEnc.inf Δt, addUp s.tEnc.sup Δt⟩, Δt := Δt,
            εP := εP, εS := εS, P := PRred })
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

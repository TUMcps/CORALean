module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Alg. 1` in floats: reachability at a fixed step, order and zonotope order

`ẋ = Ax + Bu + c`, `u(t) ∈ U` arbitrary in time, from `X₀` over `[tStart, tFinal]`, by
[1, Alg. 1] computed in `𝕋`: `N = (tFinal - tStart)/Δt` iterations from `step_manualInitFloat`,
returning `R̂(τ_0), …, R̂(τ_{N-1})`. `B` and `c` are the system's; `V = B U ⊕ c`
(`inputSetFloat`) is split at its stored center, so `0 ∈ U` is not asked. The order `η` is
raised until the float enclosures admit it (`reachOrderFloat`), as the other float reaches
raise it; `Δt` must divide the horizon exactly.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Output
* float windows of the run, if it completes

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}
open CORALean.Float FloatOps


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}

/-- Lines 5-11: one iteration of [1, Alg. 1] from `X₀` under inputs in `V`, the next state
and `R̂(τ_k)`, or `none` where no squaring count fits `[e^{At_k}]` or `[e^{At_{k+1}}]`. -/
@[step_of LinearSys.manualReachFloat]
def LinearSys.step_manualStepFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η ρ : ℕ) (s : LinearSys.ManualStateFloat 𝕋 n) :
    Option (LinearSys.ManualStateFloat 𝕋 n × Zonotope (Vec 𝕋 n)) := do
  -- 1. {ũ}, V's stored center
  let ũ := (Interval.point V.c).zonotope
  -- 1. U₀ = V - ũ, holding 0
  let Ũ := Recenter.recenter V
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  -- 3. P^u(Δt), eq. (19)
  let PuΔt := sys.inputSolutionFloat Δt η ũ
  -- 3. P̂^U(Δt), eq. (20)
  let PUΔt := sys.inputSolutionFloat Δt η Ũ
  let PuτΔt := sys.inputSolutionFloat Δt η seg                      -- P^u(τ), every τ ≤ Δt
  -- 5. t_{k+1}
  let tk1 := s.t + ToRat.toRat Δt
  -- 5. a float below t_{k+1}
  let tLo1 := addDown s.tEnc.inf Δt
  -- 5. a float above t_{k+1}
  let tHi1 := addUp s.tEnc.sup Δt
  let sq ← sys.squaringsFloat Δt s.tEnc.inf s.tEnc.sup η                    -- t_k / 2^sq within Δt
  -- 6. [e^{A t_k}] ·
  let Φtk := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (sys.expSquaringFloat s.tEnc.inf s.tEnc.sup η sq)
  -- 6. P^u(t_{k+1}), a box
  let Puk1 := (s.Pu.zonotope ⊞ Φtk PuΔt).interval
  let sq1 ← sys.squaringsFloat Δt tLo1 tHi1 η                       -- t_{k+1} / 2^sq1 within Δt
  -- 7. [e^{A t_{k+1}}] ·
  let Φtk1 := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (sys.expSquaringFloat tLo1 tHi1 η sq1)
  -- 7. H(t_{k+1})
  let Hk1 := Φtk1 X₀ ⊞ Puk1.zonotope
  -- 8.-9. Ĥ(τ_k)
  let Hτk := sys.timeIntervalFloat Δt η s.H ⊞ PuτΔt
  -- 10. P̂^U(t_{k+1})
  let PUk1 := Reduce.reduce (s.PU ⊞ Φtk PUΔt) ρ
  -- 11. R̂(τ_k)
  let Rτk := Hτk ⊞ PUk1
  pure ({ t := tk1, tEnc := ⟨tLo1, tHi1⟩, H := Hk1, Pu := Puk1, PU := PUk1 }, Rτk)

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}

/-- Lines 4-11: the windows `R̂(τ_k), …, R̂(τ_{k+K-1})` of `K` iterations from `s`. -/
@[step_of LinearSys.manualReachFloat]
def LinearSys.step_manualRunFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η ρ : ℕ) : ℕ → LinearSys.ManualStateFloat 𝕋 n → Option (List (Zonotope (Vec 𝕋 n)))
  | 0, _ => some []
  | K + 1, s => do
    let (s', Rτk) ← sys.step_manualStepFloat X₀ V Δt η ρ s               -- 5.-11. one iteration
    let Rs ← sys.step_manualRunFloat X₀ V Δt η ρ K s'                     -- 4. the rest of the loop
    pure (Rτk :: Rs)

end


/-- Lines 1-2, before the first iteration. -/
@[step_of LinearSys.manualReachFloat]
def LinearSys.step_manualInitFloat (X₀ : Zonotope (Vec 𝕋 n)) : LinearSys.ManualStateFloat 𝕋 n :=
  { t := 0, tEnc := ⟨zero, zero⟩                              -- 1. t₀ ← 0
    H := X₀                                                         -- 2. H(t₀) ← X₀
    Pu := Interval.point fun _ => zero                              -- 2. P^u(t₀) ← 0
    PU := (Interval.point fun _ => zero).zonotope }                 -- 2. P̂^U(t₀) ← 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the windows `R̂(τ_0), …, R̂(τ_{N-1})` of `ẋ = Ax + Bu + c` from `X₀` under
inputs in `U`, or `none`. -/
def LinearSys.manualReachFloat (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := sys.inputSetFloat params.U                               -- B U ⊕ c, in the state space
  -- 1.-11. the loop over the time steps, from the initial state
  sys.step_manualRunFloat X₀ V Δt η' ρ N (LinearSys.step_manualInitFloat X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

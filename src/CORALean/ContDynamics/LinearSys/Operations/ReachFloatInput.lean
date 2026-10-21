module

public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputStep
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.Global.Float.ToRat
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# Recursive reachability with inputs in floats: CORA's `priv_reach_standard`

`ẋ = Ax + Bu + c`, `u(t) ∈ U` arbitrary in time, computed in `𝕋`: `X₀`, `U` (in input space),
`Δt`, `η`, `ρ` and `N` read as `reachFloat` reads them, `B` and `c` the system's. `V = B U ⊕ c`
(`inputSetFloat`, CORA's `canonicalForm` at `W = {0}`) is split at its stored center into the
constant `ũ` and `Ũ = V - ũ ∋ 0`, so `0 ∈ U` is not asked. The constant contributes `P̃(Δt)` per
step, and `P̃^R(τ_0)` within the first window: the input set `[0, ũ]` over one step
(`inputReach_mono`). `Ũ` contributes `P^R(Δt)` per step, and the loop (`reachFloatInputStep`) runs
CORA's: `H ← reduce([e^{AΔt}] H ⊕ P̃(Δt))`, and `P^R` accumulates the propagated one-step set.
Window `k` is `H(τ_k) ⊕ P^R(t_{k+1})`; every input set is `inputSolutionFloat`.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Output
* windows and time-point sets of the run with inputs, if it completes
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

/-- The windows `R(τ_0), …, R(τ_{N-1})` and the time-point sets `R_0, …, R_N`
of `ẋ = Ax + Bu + c` from `X₀` under inputs in `U`, reducing to order `ρ`. -/
def LinearSys.reachFloatInput (sys : LinearSys 𝕋 n) (params : Reach.InputParams (Zonotope (Vec 𝕋 n))
    (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n)) × List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := sys.inputSetFloat params.U                               -- B U ⊕ c, in the state space
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let eAΔt := sys.expIntervalFloat Δt Δt η'                         -- [e^{AΔt}], once
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F], once
  let eA := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{AΔt}] ·
    (S := 𝒵[𝕋]) eAΔt
  let Pu := sys.inputSolutionFloat Δt η' ũ                          -- P̃(Δt)
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let PuR := sys.inputSolutionFloat Δt η' seg                       -- P̃^R(τ_0)
  let PU := sys.inputSolutionFloat Δt η' Ũ                          -- P^R(Δt)
  let Htp₁ := Reduce.reduce (eA X₀ ⊞ Pu) ρ                          -- H(t_1)
  let Hti₀ := (LinComb.linComb X₀ (eA X₀) ⊞                         -- H(τ_0) = H^R ⊕ P̃^R
    Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) F X₀) ⊞ PuR
  let S := List.iterate (LinearSys.reachFloatInputStep eAΔt Pu ρ)   -- the loop, k = 0 … N-1
    (Htp₁, Hti₀, PU, PU) N
  let Rti := S.map fun s => s.2.1 ⊞ s.2.2.1                         -- H(τ_k) ⊕ P^R(t_{k+1})
  let Rtp := X₀ :: S.map fun s => s.1 ⊞ s.2.2.1                     -- H(t_{k+1}) ⊕ P^R(t_{k+1})
  pure (Rti, Rtp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

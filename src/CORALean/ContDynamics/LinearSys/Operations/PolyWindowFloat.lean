module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlusAlign
public import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The window of a linear step from a polynomial zonotope, in floats

CORA's `initReach_adaptive` and `aux_deltaReach_adaptive` of `linearSys` with the start set a
polynomial zonotope: `[e^{AΔt}] X₀` keeps the dependency of `X₀` on its factors, the input
solutions are zonotopes added as independent generators (CORA's `pZ + zonotope`). The input `V`
is time-varying, its center held through `hull(0, ũ)`, so the window covers every time of the step.

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `V` – input zonotope
* `X₀` – start polynomial zonotope

## Output
* the window and the differences over the step, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ), Rdiff)` of `δ̇ = Aδ + ũ`, `ũ ∈ V`, from `X₀`: the window over the step and the set of
the differences `δ(t) - δ(0)`, or none if no Taylor order is admissible. -/
def LinearSys.polyWindowFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (V : Zonotope (Vec 𝕋 n))
    (X₀ : PolyZonotope (Vec 𝕋 n)) : Option (PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let eAΔt := sys.expIntervalFloat Δt Δt η'                         -- [e^{AΔt}]
  let eAΔtI := Interval.matPlus eAΔt (Interval.point (negIdentityMat 𝕋 n))  -- [e^{AΔt}] - I
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F]
  let PuR := (sys.inputSolutionFloat Δt η' seg).ofIndep             -- P̃^R(τ_0)
  let PU := (sys.inputSolutionFloat Δt η' Ũ).ofIndep                -- P^R(Δt)
  let FX := PolyZonotope.mtimesIntervalMat F X₀                     -- [F] X₀
  let O := (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.ofIndep    -- the origin
  pure (((LinComb.linComb X₀ (PolyZonotope.mtimesIntervalMat eAΔt X₀) ⊞ FX) ⊞ PuR) ⊞ PU,
    (LinComb.linComb O (PolyZonotope.mtimesIntervalMat eAΔtI X₀) ⊞ FX) ⊞ (PuR ⊞ PU))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

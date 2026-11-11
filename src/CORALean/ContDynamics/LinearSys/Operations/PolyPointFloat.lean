module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.DepPart
public import CORALean.ContSet.PolyZonotope.Float.Operations.IndepZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlusAlign
public import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The end set of a linear step from a polynomial zonotope, in floats

The end set `R(t_1)` of CORA's `initReach_adaptive` with the constant input `Vs`, a polynomial
zonotope over `X₀`'s factors (`priv_precompStatError_adaptive`). Its dependent part is constant over
the step, a function of the start point alone, and is added by `exactPlus` through
`[∫₀^Δt e^{As} ds]` as CORA's `errorSolution_adaptive` does, so that its dependency on `X₀` stays.
Its independent part varies with the state's input, which `[∫₀^Δt e^{As} ds]` does not bound (the
integral of a varying input is not the integral of its matrix times one value); it joins the input
`V`, whose solution bounds every input in time (a repair of CORA's constant treatment).

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `V` – input zonotope
* `X₀` – start polynomial zonotope
* `Vs` – constant input, over `X₀`'s factors

## Output
* the end set, or none
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

/-- `R(t_1)` of `δ̇ = Aδ + ũ + vs`, `ũ ∈ V`, `vs ∈ Vs`, from `X₀`, `Vs` a function of the same
point of `X₀`: `[e^{AΔt}] X₀ ⊞ₑ [∫₀^Δt e^{As} ds] Vs_dep ⊕ P̃(Δt) ⊕ P^R(Δt)`, the input `V`
widened by the independent part of `Vs`, or none. -/
def LinearSys.polyPointFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (V : Zonotope (Vec 𝕋 n))
    (X₀ Vs : PolyZonotope (Vec 𝕋 n)) : Option (PolyZonotope (Vec 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                          -- η, raised until admissible
  let Vt := V ⊞ Vs.indepZonotope                                -- V ⊕ the time-varying part of Vs
  let ũ := (Interval.point Vt.c).zonotope                       -- {ũ}, Vt's stored center
  let Ũ := Recenter.recenter Vt                                 -- Ũ = Vt - ũ, holding 0
  let Pu := (sys.inputSolutionFloat Δt η' ũ).ofIndep            -- P̃(Δt)
  let PU := (sys.inputSolutionFloat Δt η' Ũ).ofIndep            -- P^R(Δt)
  let eA := PolyZonotope.mtimesIntervalMat (sys.expIntervalFloat Δt Δt η') X₀   -- [e^{AΔt}] X₀
  let Ps := PolyZonotope.mtimesIntervalMat                      -- eAtInt * Vstat, the part
    (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η') Vs.depPart  -- constant in time
  pure ((eA.exactPlusAlign Ps) ⊞ (Pu ⊞ PU))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

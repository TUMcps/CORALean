module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.HalvingsFloat
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
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.Reduce
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The end set of a linear step from a polynomial zonotope, in floats

The end set `R(t_1)` of CORA's `initReach_adaptive` with the constant input `Vs`, a polynomial
zonotope over `X₀`'s factors (`priv_precompStatError_adaptive`). Its dependent part is constant over
the step and is added by `exactPlus` through `[∫₀^Δt e^{As} ds]` as CORA's `errorSolution_adaptive`
does, so that its dependency on `X₀` stays. Its independent part varies with the state's input,
which that matrix does not bound; it joins the input `V`, whose solution bounds every input in time.
As in CORA, the homogeneous solution and the varying input's solution are reduced at `ζ` first, the
input after being boxed to `n` generators (`reduce` to order 1). The constant input `ũ` is one
summed series matrix applied to it; the varying input's solution stays a term by term sum.

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `ζ` – reduction factor of the pieces (`zeta_z`)
* `p` – square root precision
* `V` – input zonotope
* `X₀` – start polynomial zonotope
* `Vs` – constant input, over `X₀`'s factors

## Output
* the end set, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R(t_1)` of `δ̇ = Aδ + ũ + vs`, `ũ ∈ V`, `vs ∈ Vs`, from `X₀`, `Vs` a function of the same
point of `X₀`: `[e^{AΔt}] X₀ ⊞ₑ [∫₀^Δt e^{As} ds] Vs_dep ⊕ [∫₀^Δt e^{As} ds] ũ ⊕ P^R(Δt)`, the
input `V` widened by the independent part of `Vs`, or none. -/
def LinearSys.polyPointFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (ζ : 𝕋) (p : ℕ)
    (V : Zonotope (Vec 𝕋 n)) (X₀ Vs : PolyZonotope (Vec 𝕋 n)) :
    Option (PolyZonotope (Vec 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                          -- η, raised until admissible
  let s ← sys.halvingsFloat Δt                                  -- halvings of `AΔt`
  let Vt := V ⊞ Vs.indepZonotope                                -- V ⊕ the time-varying part of Vs
  let ũ := (Interval.point Vt.c).zonotope                       -- {ũ}, Vt's stored center
  let Ũ := Recenter.recenter Vt                                 -- Ũ = Vt - ũ, holding 0
  let Pu := (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋])       -- eAtInt * ũ, the summed series
    (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η') ũ).ofIndep   -- applied to the constant
  let Ũb := Zonotope.reduce Ũ 1                                 -- Ũ boxed to `n` generators
  let PU := ((sys.inputSolutionFloat Δt η' Ũb).reduceAdaptive ζ p).ofIndep  -- reduce(P^R(Δt))
  let eA := (PolyZonotope.mtimesIntervalMat (sys.expSquaringFloat Δt Δt 16 s) X₀).reduceAdaptive
    ζ p                                                             -- reduce([e^{AΔt}] X₀)
  let Ps := PolyZonotope.mtimesIntervalMat                      -- eAtInt * Vstat, the part
    (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η') Vs.depPart  -- constant in time
  pure (((eA.exactPlusAlign Ps).compactGens ⊞ Pu) ⊞ PU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

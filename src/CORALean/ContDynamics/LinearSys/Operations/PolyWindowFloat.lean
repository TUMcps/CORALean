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
# The window of a linear step from a polynomial zonotope, in floats

CORA's `initReach_adaptive` and `aux_deltaReach_adaptive` of `linearSys` with the start set a
polynomial zonotope: `[e^{AΔt}] X₀` keeps the dependency of `X₀` on its factors, the input
solutions are zonotopes added as independent generators (CORA's `pZ + zonotope`). The input `V`
is time-varying, its center held through `hull(0, ũ)`, so the window covers every time of the step.
As CORA does, the homogeneous solution and the solutions of the inputs are reduced adaptively at
`ζ` before they are added, which keeps the independent part small. The input solutions stay term
by term sums (a summed series matrix bounds only a constant input), of the varying input `Ũ` boxed
to `n` generators first (`reduce` to order 1), as the series multiplies each generator per order.

## Inputs
* `sys` – linear system
* `Δt` – step size
* `η` – Taylor terms
* `ζ` – reduction factor of the pieces (`zeta_z`)
* `p` – square root precision
* `V` – input zonotope
* `X₀` – start polynomial zonotope

## Output
* the window and the differences over the step, or none
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

/-- `(R(τ), Rdiff)` of `δ̇ = Aδ + ũ`, `ũ ∈ V`, from `X₀`: the window over the step and the set of
the differences `δ(t) - δ(0)`, or none if no Taylor order is admissible. -/
def LinearSys.polyWindowFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (ζ : 𝕋) (p : ℕ)
    (V : Zonotope (Vec 𝕋 n)) (X₀ : PolyZonotope (Vec 𝕋 n)) :
    Option (PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n)) := do
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored center
  let Ũ := Recenter.recenter V                                      -- Ũ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let s ← sys.halvingsFloat Δt                                      -- halvings of `AΔt`
  let eAΔt := sys.expSquaringFloat Δt Δt 16 s                       -- [e^{AΔt}], tight
  let eAΔtI := Interval.matPlus eAΔt (Interval.point (negIdentityMat 𝕋 n))  -- [e^{AΔt}] - I
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F]
  let PuR := (sys.inputSolutionFloat Δt η' seg).reduceAdaptive ζ p  -- reduce(P̃^R(τ_0))
  let Ũb := Zonotope.reduce Ũ 1                                      -- Ũ boxed to `n` generators
  let PU := (sys.inputSolutionFloat Δt η' Ũb).reduceAdaptive ζ p    -- reduce(P^R(Δt))
  let FX := PolyZonotope.mtimesIntervalMat F X₀                     -- [F] X₀
  let O := (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.ofIndep    -- the origin
  let hom := (LinComb.linComb X₀ (PolyZonotope.mtimesIntervalMat eAΔt X₀) ⊞ FX).reduceAdaptive
    ζ p                                                             -- reduce(enclose + [F] X₀)
  let dhom := (LinComb.linComb O (PolyZonotope.mtimesIntervalMat eAΔtI X₀) ⊞ FX).reduceAdaptive
    ζ p                                                             -- the same for the differences
  pure ((hom ⊞ PuR.ofIndep) ⊞ PU.ofIndep, dhom ⊞ (PuR ⊞ PU).ofIndep)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachFloatOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatErrorAdaptiveFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber

@[expose] public section

/-!
# The static error follows the start point's factors

`precompStatErrorAdaptiveFloat` keeps `Vstat`, the static error `½ zᵀ H✱ z` over the reduced start
set and the input, as a polynomial zonotope on the factors of the start set, so that the end set can
add it to the free motion by `exactPlus`. What `exactPlus` needs is that, at the factors `α` of a
start point, `Vstat`'s points include the static error of that point with every input: the
dependency survives the reduction, the Cartesian product, the quadratic map and the second
reduction. Each of these keeps the factors, and holds the points it is given at them; this is not
proved here, so the theorems on the end set take it as a hypothesis.

## Inputs
* `fm` – float Hessian model
* `xs` – linearization point
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision
* `Rdelta` – start set less the linearization point

## Output
* whether the static error follows the factors of the start set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- At every value `α` of the factors of `Rdelta` and every point of `Rdelta` there, the static
error at that point and any input `μ` of `U - u✱` is a point of `Vstat` at the same `α`. -/
def NonlinearSys.FloatHessModel.HasTrackedStaticError (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (xs : Vec 𝕋 n) (U : Zonotope (Vec 𝕋 m)) (redFactor : 𝕋) (p : ℕ)
    (Rdelta : PolyZonotope (Vec 𝕋 n)) : Prop :=
  ∀ α : ℕ → ℝ, (∀ k, |α k| ≤ 1) → ∀ δ ∈ Rdelta.fiber (fun k => α k),
    ∀ μ ∈ (Recenter.recenter U).toSet,
      (fun i => Fin.append δ μ ⬝ᵥ (Scalar.toRealMat
        ((fm.hess (Interval.point xs) (Interval.point U.c) i).centerMat) *ᵥ Fin.append δ μ) / 2)
        ∈ (fm.precompStatErrorAdaptiveFloat xs U redFactor p Rdelta).1.fiber (fun k => α k)

/-- `HasTrackedStaticError` at the linearization point and the start set
`linReachPolyAdaptivePassFloat` computes from `R`. -/
def NonlinearSys.FloatHessModel.HasTrackedPassStaticError (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (redFactor : 𝕋) (p : ℕ)
    (R : PolyZonotope (Vec 𝕋 n)) : Prop :=
  let Rc : Zonotope (Vec 𝕋 n) := ⟨0, R.c, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
  let xs := (fm.toFloatModel.linPointFloat options.Δt Rc U).1
  fm.HasTrackedStaticError xs U redFactor p (R ⊞ (Interval.point (-xs)).zonotope.ofIndep)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

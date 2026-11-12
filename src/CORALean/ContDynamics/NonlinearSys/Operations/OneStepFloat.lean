module

public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedFormFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinearStep
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

@[expose] public section

/-!
# One step of a linearization, in deviation coordinates

CORA's `oneStep(linsys, Rdelta, ...)` and `Rti + p.x` in `linReach`, computed in `𝕋`: the linearized
system `δ̇ = A δ + ũ`, `ũ ∈ V` entering through the identity, run one linear step from `R - x✱`,
and both sets it returns, `R(τ_k)` and `R(t_{k+1})`, shifted back by `x✱`. The step is one of
`LinearSys.reachFloatInput` or `LinearSys.oneStepClosedFormFloat` at order `max 2 η` on `V.c` and
`V - V.c`, as `reachFloatInput` splits `V`; it needs `Δt > 0`, which `reachFloatInput` gets from its
step count. `V` is the caller's: `oneStepFloat_outer` asks that `f(x, u) - A(x - x✱)` lie in it. The
`'lin'` and `'poly'` variants differ only in the `V` they build [1, Alg. 1, line 13].

## Inputs
* `A` – state matrix
* `xs` – state expansion point
* `V` – input zonotope
* `R` – start zonotope
* `options` – reachability options
* `step` – linear step

## Output
* the time-interval and end sets, or none

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the International Conference on Hybrid Systems:
      Computation and Control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` of `δ̇ = A δ + ũ`, `ũ ∈ V`, from `R - x✱`, shifted back by
`x✱`; `none` if the linear step fails. -/
def NonlinearSys.oneStepFloat (A : Mat 𝕋 n n) (xs : Vec 𝕋 n) (V R : Zonotope (Vec 𝕋 n))
    (options : LinearSys.ReachFloatOptions 𝕋)
    (step : NonlinearSys.LinearStep := .reachFloatInput) :
    Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) := do
  let pt := fun v => (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))
  let lin : LinearSys 𝕋 n := LinearSys.canonicalFloat A  -- δ̇ = A δ + ũ, ũ ∈ V
  match step with
  | .reachFloatInput => do
    let S ← lin.reachFloatInput                                     -- one step from R - x✱
      ⟨R ⊞ pt (-xs), V, 0, ToRat.toRat options.Δt⟩ options
    let Δτ ← S.1.head?                                              -- R(τ_k) - x✱
    let Δ₁ ← S.2[1]?                                                -- R(t_{k+1}) - x✱
    pure (Δτ ⊞ pt xs, Δ₁ ⊞ pt xs)                                   -- Rti + p.x, Rtp + p.x
  | .closedForm =>
    if ltStrict zero options.Δt then do
      let S ← lin.oneStepClosedFormFloat (R ⊞ pt (-xs)) (Recenter.recenter V) V.c  -- one step from
        options.Δt (max 2 options.η)                                -- R - x✱, V = V.c ⊕ (V - V.c)
      pure (S.Rti ⊞ pt xs, S.Rtp ⊞ pt xs)                           -- Rti + p.x, Rtp + p.x
    else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

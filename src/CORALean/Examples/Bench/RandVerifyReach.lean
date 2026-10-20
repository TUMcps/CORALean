import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatInput
import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.Examples.Bench.RandVerifyAlg
import CORALean.Examples.Bench.RandVerifySystem
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

/-!
# `randverify`: the one call into the reach algorithm

The windows `R(τ_0), …, R(τ_{N-1})` of `ẋ = A x + B u` from `X0` over `[0, tFinal]`, or the reason
there are none. This is the ONLY place `randverify` reaches a reach algorithm, so that the day the
verified reach is replaced, this file alone changes.

The algorithms are `LinearSys.reachFloatInput` and `LinearSys.reachWrappingFreeFloatInput`, with `U`
the box `S.U` as a zonotope in input space and `B` apart.

## Inputs
* `alg` – reach algorithm
* `S` – system
* `tFinal` – final time
* `η` – Taylor order
* `ρ` – zonotope order

## Output
* reach windows or an error message
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows of `alg` for `S` over `[0, tFinal]` at Taylor order `η` and zonotope order `ρ`. -/
def randVerifyReach (alg : RandAlg) (S : RandSystem 𝕋) (tFinal : ℚ) (η ρ : ℕ) :
    Except String (List (Zonotope (Vec 𝕋 5))) :=
  -- the system, the problem and the algorithm's options, as CORA's `params`/`options`
  let sys : LinearSys 𝕋 5 :=                                   -- linearSys(A, B), c = 0
    { LinearSys.canonicalFloat S.A with m := 2, B := S.B, D := fun _ _ => FloatOps.zero }
  let params : Reach.InputParams (Zonotope (Vec 𝕋 5)) (Zonotope (Vec 𝕋 2)) ℚ :=
    { X₀ := S.X0, U := Interval.zonotope S.U, tFinal := tFinal }
  let options : LinearSys.ReachOptions 𝕋 :=
    { Δt := S.dt, η := η, ρ := ρ }
  -- `N = tFinal / Δt` must be a natural number, and `η` admissible, as the algorithms require
  match Reach.steps 0 tFinal (ToRat.toRat S.dt) with
  | none => throw "tFinal / dt is not a natural number"
  | some _ =>
  match sys.reachOrderFloat S.dt S.dt η with
  | none => throw s!"no admissible Taylor order (from max {η} 2) found within the search bound"
  | some _ =>
  -- the windows of the chosen algorithm
  match alg with
  | .standard =>
    match sys.reachFloatInput params options with
    | some (Rti, _) => pure Rti
    | none => throw "reachFloatInput returned none (a window's squaring search failed)"
  | .wrappingFree =>
    match sys.reachWrappingFreeFloatInput params options with
    | some Rti => pure Rti
    | none => throw "reachWrappingFreeFloatInput returned none (a window's squaring search failed)"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

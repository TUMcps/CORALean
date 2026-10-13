module

public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
public import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.reachFloat`

CORA's `location/reach`, its continuous part: the time-interval sets of a stay
of length up to `tFinal` from `X₀`, by `LinearSys.reachFloatInput` at the
location's dynamics, its inputs `ℓ.U` entering through the identity. A stay
may end at any of those times, so every set is returned and none is cut to the
invariant; `Location.guardIntersectFloat` cuts them where a guard is tested.

`none` when `tFinal` is not positive, as well as where `reachFloatInput` fails:
a horizon of zero steps has no window to hold the stay's one state.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {G : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-interval sets `R(τ_0), …, R(τ_{N-1})` of a stay in `ℓ` from `X₀`, `N Δt = tFinal`. -/
def Location.reachFloat (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n) (tFinal : ℚ)
    (options : LinearSys.ReachOptions 𝕋) (X₀ : Zonotope (Vec 𝕋 n)) : Option
    (List (Zonotope (Vec 𝕋 n))) :=
  if tFinal ≤ 0 then none else do                                  -- a stay of positive length
  let (Rti, _) ← ℓ.dynamics.reachFloatInput (identityMat 𝕋 n)     -- ẋ = A x + I u, u ∈ ℓ.U
    ⟨X₀, ℓ.U, 0, tFinal⟩ options
  pure Rti

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

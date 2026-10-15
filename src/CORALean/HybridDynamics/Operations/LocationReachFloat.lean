module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.HybridDynamics.Operations.InputSetFloat

@[expose] public section

/-!
# `Location.reachFloat`

CORA's `location/reach`, its continuous part: the time-interval sets of a stay
of length up to `tFinal` from `X₀`, by `LinearSys.reachFloatInput` at the canonical form of the
location's dynamics, as CORA's `linearSys/reach` runs on `canonicalForm`: `ẋ = A x + u'`, the
combined input `u' = B u + c + E w` in `inputSetFloat`, entering through the identity. A stay
may end at any of those times, so every set is returned and none is cut to the
invariant; `Location.guardIntersectFloat` cuts them where a guard is tested.

`none` when `tFinal` is not positive, as well as where `reachFloatInput` fails:
a horizon of zero steps has no window to hold the stay's one state.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {G : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-interval sets `R(τ_0), …, R(τ_{N-1})` of a stay in `ℓ` from `X₀`, `N Δt = tFinal`. -/
def Location.reachFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n) (tFinal : ℚ)
    (options : LinearSys.ReachOptions 𝕋) (X₀ : Zonotope (Vec 𝕋 n)) : Option
    (List (Zonotope (Vec 𝕋 n))) :=
  if tFinal ≤ 0 then none else do                                  -- a stay of positive length
  let (Rti, _) ← (LinearSys.canonicalFloat ℓ.dynamics.A).reachFloatInput  -- ẋ = A x + u'
    ⟨X₀, ℓ.inputSetFloat, 0, tFinal⟩ options                        -- u' ∈ B U ⊕ c ⊕ E W
  pure Rti

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

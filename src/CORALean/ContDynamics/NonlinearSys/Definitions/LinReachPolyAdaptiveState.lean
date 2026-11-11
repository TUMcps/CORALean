module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# What one step of CORA's adaptive `'poly'` algorithm hands the next

`LinReachPolyAdaptiveState`: as `LinReachAdaptiveState`, with polynomial zonotopes for the sets and
without what `'lin'` alone tunes (`tensorOrder`, `kappa_*`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- What a step of CORA's `poly-adaptive` hands the next: sets, time, and tuning state. -/
structure NonlinearSys.LinReachPolyAdaptiveState (𝕋 : Type) (n : ℕ) where
  /-- `options.i`, the number of the step about to be taken. -/
  i : ℕ
  /-- `options.t`, exactly. -/
  t : ℚ
  /-- `options.R`, the time-point set the next step starts from. -/
  R : PolyZonotope (Vec 𝕋 n)
  /-- The time-interval set of the last step. -/
  Rτ : PolyZonotope (Vec 𝕋 n)
  /-- `options.timeStep`, the size of the last step. -/
  timeStep : 𝕋
  /-- `options.finitehorizon(i-1)`. -/
  finitehorizon : 𝕋
  /-- `options.varphi(i-1)`. -/
  varphi : 𝕋
  /-- `options.error_adm_horizon`. -/
  errAdmHorizon : Vec 𝕋 n
  /-- `options.error_adm_Deltatopt`. -/
  errAdmDeltatopt : Vec 𝕋 n
  /-- `options.orders`, `none` for `Inf`. -/
  orders : Fin n → Option ℕ
  /-- `options.minorder`. -/
  minorder : ℕ
  /-- `options.zeroWidthDim`. -/
  zeroWidthDim : Fin n → Bool
  /-- `tVec`, latest first. -/
  steps : List 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

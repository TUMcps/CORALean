module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# What one step of CORA's adaptive `'lin'` algorithm hands the next

`LinReachAdaptiveState`: the step's reachable sets, and the fields of CORA's `options` that
`linReach_adaptive` writes for the step after it (`timeStep`, `finitehorizon(i)`, `varphi(i)`, the
admissible errors, `tensorOrder`, `orders`, `minorder`, `zeroWidthDim`, `kappa_*`). The time `t`
is kept exactly; `steps` are the step sizes so far, latest first, for `aux_checkForAbortion`. An
order `none` is CORA's `Inf`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- What a step of CORA's `lin-adaptive` hands the next: sets, time, and tuning state. -/
structure NonlinearSys.LinReachAdaptiveState (𝕋 : Type) (n : ℕ) where
  /-- `options.i`, the number of the step about to be taken. -/
  i : ℕ
  /-- `options.t`, exactly. -/
  t : ℚ
  /-- `options.R`, the time-point set the next step starts from. -/
  R : Zonotope (Vec 𝕋 n)
  /-- The time-interval set of the last step. -/
  Rτ : Zonotope (Vec 𝕋 n)
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
  /-- `options.tensorOrder`, `2` or `3`. -/
  tensorOrder : ℕ
  /-- `options.orders`, `none` for `Inf`. -/
  orders : Fin n → Option ℕ
  /-- `options.minorder`. -/
  minorder : ℕ
  /-- `options.zeroWidthDim`. -/
  zeroWidthDim : Fin n → Bool
  /-- `options.kappa_deltat`. -/
  kappaDeltat : 𝕋
  /-- `options.kappa_abstrerr`. -/
  kappaAbstrerr : 𝕋
  /-- `tVec`, latest first. -/
  steps : List 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

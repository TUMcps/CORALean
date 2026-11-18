module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The state a zonotope verification pass carries from step to step

At `t_k`: the zonotope `⟨c, G⟩` of the initial set and the constant input carried to `t_k`, within
the scaled error `h`; the float `Φ` of `e^{A t_k}` within the scaled error `φ`; the generators and
the box of the varying input's solution up to `t_k`, within the scaled error `ρ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The pass's state at `t_k` for `n` states and `m` generators of the initial set. -/
structure LinearSys.VerifyZonoState (𝕋 : Type) (n m : ℕ) where
  /-- The center carried to `t_k`. -/
  c : Vec 𝕋 n
  /-- The generators carried to `t_k`. -/
  G : Mat 𝕋 n m
  /-- The bound of its scaled error. -/
  h : 𝕋
  /-- The float `e^{A t_k}`. -/
  Φ : Mat 𝕋 n n
  /-- The bound of its scaled error. -/
  φ : 𝕋
  /-- The generators of the varying input's solution. -/
  P : List (Vec 𝕋 n)
  /-- The box of the varying input's solution. -/
  b : Vec 𝕋 n
  /-- The bound of its scaled error. -/
  ρ : 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

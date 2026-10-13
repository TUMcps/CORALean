import CORALean.ContDynamics.NonlinearARX.Operations.Feed

/-!
# `NonlinearARX.feed` at the scalar `𝕋`

The input signal the converted system sees: block `a` holds `u(k+a)`, as `feed` at ℝ, here
on stored `𝕋` values, which is all a float run has.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} {du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `NonlinearARX.feed` at the scalar `𝕋`: block `a` holds `u(k+a)`. -/
def NonlinearARX.feedFloat (p : ℕ) (u : ℕ → Vec 𝕋 du) (k : ℕ) : Vec 𝕋 ((p + 1) * du) :=
  fun r => u (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

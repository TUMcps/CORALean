import CORALean.ContDynamics.NonlinearARX.NonlinearARX

/-!
# The input signal of the converted system

At step `k` the window moves to `y(k+1..k+p)`, and `y(k+p)` reads the inputs
`u(k+p), …, u(k)`; `feed u k` stacks them oldest first, block `a` holding `u(k+a)`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.feed (p : ℕ) (u : ℕ → Vec ℝ du) (k : ℕ) : Vec ℝ ((p + 1) * du) :=
  fun r => u (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX

@[expose] public section

/-!
# The input signal of the converted system

At step `k` the window moves to `y(k+1..k+p)`, and `y(k+p)` reads the inputs
`u(k+p), …, u(k)`; `feed u k` stacks them oldest first, block `a` holding `u(k+a)`. It is
generic in the scalar: at ℝ the input signal of the converted system, at a float type the stored
values a float run has.

## Inputs
* `p` – number of lags
* `u` – inputs
* `k` – step

## Output
* the stacked inputs of the converted system at step `k`
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   13-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} {du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.feed (p : ℕ) (u : ℕ → Vec 𝕋 du) (k : ℕ) : Vec 𝕋 ((p + 1) * du) :=
  fun r => u (k + (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

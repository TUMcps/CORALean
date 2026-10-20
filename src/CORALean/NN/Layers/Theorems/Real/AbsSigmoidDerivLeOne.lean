module

public import CORALean.NN.Layers.Theorems.Real.Basic

@[expose] public section

/-!
# The logistic function's derivative is at most one

A product of two sigmoids, so inside `(0, 1)` on all of ℝ: the global bound a refinement
level's fit is chosen against.

## Inputs
* `t` – real number

## Hypotheses
* none

## Conclusion
* the sigmoid's derivative is at most one in absolute value
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_sigmoidDeriv_le_one (t : ℝ) : -- --- CONCL ---
    |sigmoidDeriv t| ≤ 1 := by -- --- PROOF ---
  have h1 := sigmoid_pos t
  have h2 := sigmoid_pos (-t)
  have h3 := sigmoid_lt_one t
  have h4 := sigmoid_lt_one (-t)
  show |sigmoid t * sigmoid (-t)| ≤ 1
  rw [abs_le]
  exact ⟨by nlinarith, by nlinarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

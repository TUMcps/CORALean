module

public import CORALean.ContSet.Zonotope.Real.Operations.Recenter

@[expose] public section

/-!
# The recentered zonotope contains the origin

At zero coefficients. `recenter` states its own `h`, that counts only up to
unfolding, so the sum needs a `show`.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the origin lies in the recentered zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zero_mem_recenter (Z : Zonotope α) : (0 : α) ∈ Z.recenter.construct := by
  refine ⟨0, fun _ => by simp, ?_⟩
  show (0 : α) = 0 + ∑ j, (0 : Fin Z.h → ℝ) j • Z.G j
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

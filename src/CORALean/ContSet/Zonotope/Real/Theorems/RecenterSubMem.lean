module

public import CORALean.ContSet.Zonotope.Real.Operations.Recenter
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# A member shifted by the center is a member of the recentered zonotope

Each states its own `h`, that counts only up to unfolding, so the sum needs a
`show`.

## Inputs
* `Z` – zonotope
* `y` – point

## Hypotheses
* `hy` – `y` lies in `Z`

## Conclusion
* `y` minus the center lies in the recentered zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sub_center_mem_recenter {Z : Zonotope α} {y : α}
    (hy : y ∈ Z.construct) : -- --- CONCL ---
    y - Z.c ∈ Z.recenter.construct := by -- --- PROOF ---
  obtain ⟨β, hβ, hy⟩ := hy
  refine ⟨β, hβ, ?_⟩
  rw [hy]
  show Z.c + ∑ j, β j • Z.G j - Z.c = 0 + ∑ j, β j • Z.G j
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

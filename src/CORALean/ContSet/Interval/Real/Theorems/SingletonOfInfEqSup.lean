module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A box with equal bounds is a single point

Every coordinate is squeezed between two equal bounds.

## Inputs
* `I` – interval

## Hypotheses
* `h` – bounds equal

## Conclusion
* the interval is the single point of its bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.construct_eq_singleton_of_inf_eq_sup {I : Interval α}
    (h : I.inf = I.sup) : -- --- CONCL ---
    I.construct = {I.inf} := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    refine Entrywise.ext fun i => le_antisymm ?_ (hx i).1
    have := (hx i).2
    rwa [← h] at this
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fun i => ⟨le_refl _, by rw [h]⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

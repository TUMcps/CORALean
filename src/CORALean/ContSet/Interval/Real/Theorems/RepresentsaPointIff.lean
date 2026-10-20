module

public import CORALean.ContSet.Interval.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Real.Theorems.ConstructEqSingleton
public import CORALean.ContSet.Interval.Real.Theorems.SingletonOfInfEqSup

@[expose] public section

/-!
# `Interval.representsa_point` is being a single point

Both bounds equal is a single point, and a single point forces both bounds onto it.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the test holds iff the interval is a single point
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

theorem Interval.representsa_point_iff (I : Interval α) : -- --- CONCL ---
    I.representsa_point ↔ ∃ v, I.construct = {v} := by -- --- PROOF ---
  constructor
  · intro h
    exact ⟨I.inf, Interval.construct_eq_singleton_of_inf_eq_sup h⟩
  · rintro ⟨v, hv⟩
    have h := Interval.inf_sup_of_construct_eq_singleton hv
    exact h.1.trans h.2.symm


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

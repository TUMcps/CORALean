module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.ConstructEqSingleton
public import CORALean.ContSet.Interval.Real.Theorems.SingletonOfInfEqSup

@[expose] public section

/-!
# `Interval.representsa_origin` is being the origin

Both bounds zero is the single point `0`, and the single point `0` forces both bounds to `0`.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the test holds iff the interval is the origin
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

theorem Interval.representsa_origin_iff (I : Interval α) :
    I.representsa_origin ↔ I.construct = {0} := by -- --- PROOF ---
  constructor
  · rintro ⟨h₁, h₂⟩
    have h : I.inf = I.sup := h₁.trans h₂.symm
    rw [Interval.construct_eq_singleton_of_inf_eq_sup h, h₁]
  · intro h
    exact Interval.inf_sup_of_construct_eq_singleton h


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

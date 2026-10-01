import CORALean.ContSet.Interval.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Interval.Real.Theorems.ConstructEqSingleton
import CORALean.ContSet.Interval.Real.Theorems.SingletonOfInfEqSup

/-!
# `Interval.representsa_origin` is being the origin

Both bounds zero is the single point `0`, and the single point `0` forces both bounds to `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

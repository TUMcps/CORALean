module

public import CORALean.ContSet.Equality.Float.Operations.Basic

@[expose] public section

/-!
# `ContSet/Equality/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `ContSet.eqBool_sound`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open CORALean

variable {S α : Type} [ContSet S α] [Isequal S] [DecidableRel (Isequal.isequal (S := S))]

/-- `true` says the class's `isequal` holds, which says the two representations denote one set. -/
theorem ContSet.eqBool_sound {s t : S} (h : ContSet.eqBool s t = true) :
    ContSet.construct s = ContSet.construct t :=
  Isequal.isequal_construct s t (of_decide_eq_true h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Equality.Float.Operations.EqBool

/-!
# `ContSet.eqBool` is sound

`true` says the class's `isequal` holds, which says the two representations denote one set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean

variable {S α : Type} [ContSet S α] [Isequal S] [DecidableRel (Isequal.isequal (S := S))]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.eqBool_sound {s t : S} (h : ContSet.eqBool s t = true) :
    ContSet.construct s = ContSet.construct t :=
  Isequal.isequal_construct s t (of_decide_eq_true h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

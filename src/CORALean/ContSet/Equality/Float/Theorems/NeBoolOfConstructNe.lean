import CORALean.ContSet.Equality.Float.Operations.NeBool
import CORALean.ContSet.Equality.Float.Theorems.EqBoolSound

/-!
# `ContSet.neBool` holds of sets that differ

If the denoted sets differ, `neBool` is `true`. Only this direction: it can be `true` of two
representations of one set, since `isequal` is conservative.
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

theorem ContSet.neBool_of_construct_ne {s t : S} (h : ContSet.construct s ≠ ContSet.construct t) :
    ContSet.neBool s t = true := by
  unfold ContSet.neBool
  cases hb : ContSet.eqBool s t
  · rfl
  · exact absurd (ContSet.eqBool_sound hb) h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

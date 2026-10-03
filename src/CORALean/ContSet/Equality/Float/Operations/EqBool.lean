import CORALean.ContSet.ContSet.Operations.Eq

/-!
# CORA's `eq`, as a `Bool`

`ContSet.eq` is a `Prop`; this reads it as a run: the class's conservative `isequal`, decided.
For a float representation the `isequal` is the certified structural test, so `true` is a proof
that the two sets are equal and `false` refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean

variable {S α : Type} [ContSet S α] [Isequal S] [DecidableRel (Isequal.isequal (S := S))]


-- =====================================  MAIN DEFINITION  ====================================== --

def ContSet.eqBool (s t : S) : Bool := decide (Isequal.isequal s t)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

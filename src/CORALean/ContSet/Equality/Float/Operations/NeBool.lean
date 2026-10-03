import CORALean.ContSet.Equality.Float.Operations.EqBool
import CORALean.ContSet.ContSet.Operations.Ne

/-!
# CORA's `ne`, as a `Bool`

The negation of `ContSet.eqBool`, as CORA's `ne` is `~isequal`.
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

def ContSet.neBool (s t : S) : Bool := !ContSet.eqBool s t

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

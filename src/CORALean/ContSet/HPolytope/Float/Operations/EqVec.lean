import CORALean.ContSet.HPolytope.Float.Operations.EqScalar

/-!
# `eqVec`: two rows certified equal

Every entry `eqScalar`: the exact test for equal (or, against a negated row, inverted) rows that
`compact_` makes, where CORA's is `withinTol` at its tolerance.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- All entries `eqScalar`. -/
def HPolytope.eqVec (u v : Vec 𝕋 n) : Bool :=
  (List.finRange n).all fun j => HPolytope.eqScalar (u j) (v j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.HPolytope.Float.Operations.EqScalar

/-!
# `isZeroVec`: a row certified zero

Every entry certified equal to `zero`: CORA's `withinTol(row, 0)` at tolerance zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- All entries `eqScalar` to `zero`. -/
def HPolytope.isZeroVec (v : Vec 𝕋 n) : Bool :=
  (List.finRange n).all fun j => HPolytope.eqScalar (v j) zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

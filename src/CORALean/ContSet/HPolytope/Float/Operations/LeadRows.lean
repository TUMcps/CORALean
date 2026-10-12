import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair

/-!
# `HPolytope.leadRows`: one row of each inverted pair

The rows `i` with an inverted partner `j ≥ i`, in order: the lesser index of each pair, which
`'AtoAe'` turns into an equality. CORA's loop appends a row again when an earlier row already moved
its partner; here each row is listed once.
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

/-- The rows with an inverted partner of no smaller index. -/
def HPolytope.leadRows (Q : HPolytope 𝕋 n) : List (Fin Q.m) :=
  (List.finRange Q.m).filter fun i =>
    (List.finRange Q.m).any fun j => HPolytope.isInvertedPair Q i j && decide (i ≤ j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

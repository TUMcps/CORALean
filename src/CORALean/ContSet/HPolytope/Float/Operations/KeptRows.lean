import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair

/-!
# `HPolytope.keptRows`: the inequality rows not part of an inverted pair

The rows `i` for which no `j` is certified inverted to them, in order: what `'AtoAe'` keeps as
inequalities.
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

/-- The rows with no inverted partner. -/
def HPolytope.keptRows (Q : HPolytope 𝕋 n) : List (Fin Q.m) :=
  (List.finRange Q.m).filter fun i =>
    !(List.finRange Q.m).any fun j => HPolytope.isInvertedPair Q i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

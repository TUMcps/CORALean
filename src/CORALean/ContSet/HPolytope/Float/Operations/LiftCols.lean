import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.liftCols`

CORA's `A(:,dims) = A`: column `j` of the result is column `k` of `M` where `dims k = j`, and `0`
where no `k` does. Nothing is added, so nothing rounds. The search for `k` is `List.find?`, so the
matrix computes; for an injective `dims` it is the one preimage.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.liftCols (dims : Fin n → Fin N) (M : Mat 𝕋 m n) : Mat 𝕋 m N := fun i j =>
  match (List.finRange n).find? (fun k => dims k = j) with
  | some k => M i k
  | none => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

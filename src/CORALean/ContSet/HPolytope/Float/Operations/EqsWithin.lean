module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.eqsWithin`: equality rows known up to their slack

`HPolytope.eqs` with the equality slack given: the rows `|Aeᵢ x - beᵢ| ≤ |eᵢ|`, no inequalities
and the origin box. What an operation builds when it computes equality rows whose right-hand
sides, or the rows they came from, already carry a rounding (#218); at `e = 0` it denotes
`HPolytope.eqs`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The equalities `Ae x = be`, each within the slack `e`. -/
def HPolytope.eqsWithin (Ae : Mat 𝕋 q n) (be e : Vec 𝕋 q) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := q
  Ae := Ae
  be := be
  b_error := fun i => i.elim0
  be_error := e
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

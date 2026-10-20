module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.boxToSlack`

The error box moved into the slacks, the rows as stored. A box point adds to row `a` at most
`errUp a` (`HPolytope.le_errUp`), so an inequality's slack grows by that much; an equality's
grows by the larger of `errUp Aeᵢ` and `errUp (-Aeᵢ)`, since the box can move its reading either
way. Unlike `absorbRounding` it keeps `b`, `be` and every equality as stored: the result is the
same rows with wider slacks and the origin box, which is what `intersection` stacks.

## Inputs
* `P` – H-polytope

## Output
* `P` with its error box paid into the slacks, rounded up, and the origin box
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` with its error box paid into the slacks, rounded up, and the origin box. -/
def HPolytope.boxToSlack (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  { P with
    b_error := fun i => addUp (absolute (P.b_error i)) (P.errUp (P.A i))
    be_error := fun i =>
      addUp (absolute (P.be_error i)) (maximum (P.errUp (P.Ae i)) (P.errUp (-(P.Ae i))))
    I_error := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding

@[expose] public section

/-!
# `HPolytope.not`, over a floating-point scalar

CORA's `not(P)` for a polytope given by a single inequality `a x ≤ b`: the polytope
`-a x ≤ -b - ε`, the closed approximation of the open complement `a x > b` that stays `ε` away
from the boundary. The other cases CORA handles (an empty polytope maps to the full space, a full
space to the empty set) need its emptiness test, and any other polytope throws; here they answer
`none`. The row is read with the error box folded in (`absorbRounding`).

## Inputs
* `P` – H-polytope
* `ε` – scalar

## Output
* the right-hand side is rounded down, so the result is the smaller set
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand side is rounded down, so the result is the smaller set. -/
def HPolytope.not (P : HPolytope 𝕋 (Vec 𝕋 n)) (ε : 𝕋) : Option (HPolytope 𝕋 (Vec 𝕋 n)) :=
  let Q := P.absorbRounding
  if h : Q.m = 1 ∧ Q.me = 0 then
    some
      { m := 1
        A := fun _ j => neg (Q.A (Fin.cast h.1.symm 0) j)
        b := fun _ => subDown (neg (Q.b (Fin.cast h.1.symm 0))) ε
        me := 0
        Ae := fun i => i.elim0
        be := fun i => i.elim0
        b_error := fun _ => zero
        be_error := fun _ => zero
        I_error := Interval.origin n }
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

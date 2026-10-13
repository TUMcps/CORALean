import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.not`, over a floating-point scalar

CORA's `not(P)` for a polytope given by a single inequality `a x ≤ b`: the polytope
`-a x ≤ -b - ε`, the closed approximation of the open complement `a x > b` that stays `ε` away
from the boundary. The other cases CORA handles (an empty polytope maps to the full space, a full
space to the empty set) need its emptiness test, and any other polytope throws; here they answer
`none`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand side is rounded down, so the result is the smaller set. -/
def HPolytope.not (P : HPolytope 𝕋 (Vec 𝕋 n)) (ε : 𝕋) : Option (HPolytope 𝕋 (Vec 𝕋 n)) :=
  if h : P.m = 1 ∧ P.me = 0 then
    some
      { m := 1
        A := fun _ j => neg (P.A (Fin.cast h.1.symm 0) j)
        b := fun _ => subDown (neg (P.b (Fin.cast h.1.symm 0))) ε
        me := 0
        Ae := fun i => i.elim0
        be := ⟨fun i => i.elim0, fun i => i.elim0⟩ }
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

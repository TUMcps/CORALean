module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope

@[expose] public section

/-!
# `ConZonotope.zeroFeasible`: the centre is a point of the set

A test on the constraint rows alone that coefficients `0` meet them: every inequality's bound
is at least `0` and every equality's interval holds `0`. Then the centre is a point of the
nominal part, so the set is nonempty (`zeroFeasible_nonempty`). Sufficient, not necessary:
`false` says only that the centre may be outside.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether coefficients `0` meet every row. -/
def ConZonotope.zeroFeasible (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Bool :=
  (List.finRange cZ.P.m).all (fun i => le zero (cZ.P.b i))
    && (List.finRange cZ.P.me).all
      (fun i => le (cZ.P.be.inf i) zero && le zero (cZ.P.be.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

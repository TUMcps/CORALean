module

public import CORALean.ContSet.HPolytope.Float.Operations.EqVec

@[expose] public section

/-!
# `HPolytope.isInvertedPair`: two inequality rows certified inverted

Rows `i` and `j` with `[aⱼ, bⱼ] = -[aᵢ, bᵢ]`, certified entry by entry (`eqVec`, `eqScalar`) in both
directions, so the test is symmetric as a `Bool`: CORA's `idxInverted`, at tolerance zero. The
row `0 ≤ 0` is inverted with itself. Both slacks must be certified `zero` as well: a pair with
slack is a slab, not the equality `pairsToEq` writes it as.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[aⱼ, bⱼ] = -[aᵢ, bᵢ]` and `[aᵢ, bᵢ] = -[aⱼ, bⱼ]`, each certified. -/
def HPolytope.isInvertedPair (Q : HPolytope 𝕋 (Vec 𝕋 n)) (i j : Fin Q.m) : Bool :=
  HPolytope.eqVec (Q.A j) (-(Q.A i)) && HPolytope.eqScalar (Q.b j) (neg (Q.b i)) &&
    HPolytope.eqVec (Q.A i) (-(Q.A j)) && HPolytope.eqScalar (Q.b i) (neg (Q.b j)) &&
    (HPolytope.eqScalar (Q.b_error i) zero && HPolytope.eqScalar (Q.b_error j) zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.excludesPoint`, over a floating-point scalar

A point certified outside: some inequality `aᵀx ≤ b` whose left side, rounded down, is strictly
above `b`, or some equality row whose rounded dot product is strictly outside its interval.
Sufficient only: `true` proves the point is outside, `false` decides nothing, since `le` and
`ltStrict` agree with the reals in one direction only.
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

def HPolytope.excludesPoint (P : HPolytope 𝕋 n) (x : Vec 𝕋 n) : Bool :=
  -- an inequality violated: b < Aᵢ x
  (List.finRange P.m).any (fun i => ltStrict (P.b i) (dotDown (P.A i) x))
    -- an equality violated: be.sup < Aeᵢ x, or Aeᵢ x < be.inf
    || (List.finRange P.me).any fun i =>
      ltStrict (P.be.sup i) (dotDown (P.Ae i) x) || ltStrict (dotUp (P.Ae i) x) (P.be.inf i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

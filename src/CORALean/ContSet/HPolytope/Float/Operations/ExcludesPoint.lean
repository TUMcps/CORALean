module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.excludesPoint`, over a floating-point scalar

A point certified outside: some inequality `aᵀx ≤ b` whose left side, rounded down, is strictly
above `b`, or some equality row whose rounded dot product is strictly outside the two
inequalities it stands for. The bounds are the right-hand sides with the error box folded in
(`bU`, `beU`, `beLN`), so a point of the inflated polytope is never excluded. Sufficient only:
`true` proves the point is outside, `false` decides nothing, since `le` and `ltStrict` agree with
the reals in one direction only.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.excludesPoint (P : HPolytope 𝕋 (Vec 𝕋 n)) (x : Vec 𝕋 n) : Bool :=
  -- an inequality violated: bU < Aᵢ x
  (List.finRange P.m).any (fun i => ltStrict (P.bU i) (dotDown (P.A i) x))
    -- an equality violated: beU < Aeᵢ x, or beLN < -Aeᵢ x
    || (List.finRange P.me).any fun i =>
      ltStrict (P.beU i) (dotDown (P.Ae i) x)
        || ltStrict (P.beLN i) (dotDown (-(P.Ae i)) x)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

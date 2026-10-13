module

public import CORALean.ContSet.Zonotope.Float.Operations.RightInvQ

@[expose] public section

/-!
# `Zonotope.ballCert`

The check that a float generator matrix `G` (`n × h`) reaches a whole box with coefficients of
size at most `δ`: a candidate right inverse `H` (`h × n`) with `rightInvQ G H ≤ 1/2`, and a radius
`B > 0` with `2 B ∑ₖ |Hⱼₖ| ≤ δ` for every row `j`, every product rounded up. Then every vector
whose entries are at most `B` in magnitude is `G β` with every `|βⱼ| ≤ δ`
(`Zonotope.ballCert_reach`), which is what places a point in, or an open set inside, a zonotope
without an exact solve. `true` is a proof, `false` says only that this `H` and `B` were not good
enough.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.ballCert (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) (B δ : 𝕋) : Bool :=
  ltStrict zero B && le (Zonotope.rightInvQ G H) (half one)
    && (List.finRange h).all fun j => le (mulUp (addUp B B) (radius H j)) δ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

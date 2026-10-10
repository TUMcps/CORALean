import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint

/-!
# `Zonotope.interiorPoint`, over a floating-point scalar

`Zonotope.containsPoint` with the point strictly inside the certified box (`ltStrict` on
`Zonotope.deviation`): then the point is interior to the set, not merely in it. This is what a
bundle of zonotopes needs, as it asks one point to be interior to every member.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.interiorPoint (Z : Zonotope 𝕋 n) (H : Mat 𝕋 Z.h n) (p : Vec 𝕋 n) : Bool :=
  Zonotope.ballCert (fun i j => Z.G j i) H (Zonotope.ballB H one) one
    && ltStrict (Zonotope.deviation p Z.E.inf Z.c Z.c) (Zonotope.ballB H one)
    && (List.finRange n).all fun i => le (Z.E.inf i) (Z.E.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

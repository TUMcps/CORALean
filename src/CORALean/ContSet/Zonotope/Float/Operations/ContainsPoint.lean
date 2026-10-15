module

public import CORALean.ContSet.Zonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.Zonotope.Float.Operations.Deviation

@[expose] public section

/-!
# `Zonotope.containsPoint`, over a floating-point scalar

A point certified inside, by a right inverse `H` the caller proposes: `Zonotope.ballCert` makes the
box of radius `B` around the center part of the nominal zonotope, and the point, moved by the error
box's lower corner, is checked to lie in it (`Zonotope.deviation`, rounded upward). No exact solve
`G β = p - c` is needed; the box absorbs the rounding. Sufficient only: `true` proves membership.
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

def Zonotope.containsPoint (Z : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z.h n) (p : Vec 𝕋 n) : Bool :=
  Zonotope.ballCert (fun i j => Z.G j i) H (Zonotope.ballB H one) one
    && le (Zonotope.deviation p Z.I_error.inf Z.c Z.c) (Zonotope.ballB H one)
    && (List.finRange n).all fun i => le (Z.I_error.inf i) (Z.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

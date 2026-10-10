import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint

/-!
# `ZonoBundle.containsPoint`, over a floating-point scalar

A point is in a bundle when it is in every member: each is certified by `Zonotope.containsPoint`,
with one right inverse `Hᵢ` per member that the caller proposes. `true` proves membership; `false`
refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.containsPoint (zB : ZonoBundle 𝕋 n) (H : (i : Fin zB.k) → Mat 𝕋 (zB.Z i).h n)
    (p : Vec 𝕋 n) : Bool :=
  (List.finRange zB.k).all fun i => Zonotope.containsPoint (zB.Z i) (H i) p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

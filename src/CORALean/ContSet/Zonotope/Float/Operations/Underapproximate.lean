import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint
import CORALean.ContSet.Zonotope.Float.Operations.UnderapproximateCandidate

/-!
# `Zonotope.underapproximate`, over a floating-point scalar

CORA's `@zonotope/underapproximate(Z, S)`: for the direction `S i` the vertex
`c ± Σⱼ sign(S iᵀ gⱼ) gⱼ`. Here the candidate is computed in floats (one named `let` per step of
the real definition `Real.Zonotope.underapproximate`), and rounding may move it off the vertex; so
it is returned only if `Zonotope.containsPoint`, with a right inverse `H` of the generators the
caller proposes, certifies it inside the zonotope, else `none`. Sufficient only: `some` proves the
point is a member, `none` refutes nothing.
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

def Zonotope.underapproximate (Z : Zonotope 𝕋 n) (H : Mat 𝕋 Z.h n) (s : Vec 𝕋 n) (b : Bool) :
    Option (Vec 𝕋 n) :=
  let p := Z.underapproximateCandidate s b
  if Z.containsPoint H p then some p else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

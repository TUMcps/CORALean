import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.ContSet.Operations.EnlargeScalar

/-!
# `ZonoBundle.enlarge`, over a floating-point scalar

CORA's `@zonoBundle/enlarge.m`: each zonotope enlarged about its own centre, by the scalar-point
`ContSet.enlargeScalar` the float zonotope instantiates. The result is the intersection of the
enlarged members, not the enlargement of the intersection (the centres differ).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.enlarge (zB : ZonoBundle 𝕋 n) (factor : Vec 𝕋 n) : ZonoBundle 𝕋 n where
  k := zB.k
  Z := fun i => ContSet.enlargeScalar (S := Zonotope 𝕋) (zB.Z i) factor

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

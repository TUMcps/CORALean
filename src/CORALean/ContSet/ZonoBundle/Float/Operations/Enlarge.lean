module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.ContSet.Operations.EnlargeScalar

@[expose] public section

/-!
# `ZonoBundle.enlarge`, over a floating-point scalar

CORA's `@zonoBundle/enlarge.m`: each zonotope enlarged about its own centre, by the scalar-point
`ContSet.enlargeScalar` the float zonotope instantiates. The result is the intersection of the
enlarged members, not the enlargement of the intersection (the centres differ).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.enlarge (zB : ZonoBundle (Vec 𝕋 n)) (factor : Vec 𝕋 n) : ZonoBundle (Vec 𝕋 n) where
  k := zB.k
  Z := fun i => ContSet.enlargeScalar (S := 𝒵[𝕋]) (zB.Z i) factor

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

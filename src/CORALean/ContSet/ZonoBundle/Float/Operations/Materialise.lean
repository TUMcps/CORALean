module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise

@[expose] public section

/-!
# `ZonoBundle.materialise`

A member's fields are function types and so is the family, so the bundle an
operation returns is a closure over the one it was given and a loop pays for its
whole history on every entry read. `materialise` stores the family and every
member in it; `materialise_eq` says it is the identity, which is what each proof
in `Instances` rewrites with, exactly as `Zonotope`'s does.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.materialise (zB : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) :=
  let Z : Vector (Zonotope (Vec 𝕋 n)) zB.k := Vector.ofFn fun i => Zonotope.materialise (zB.Z i)
  { k := zB.k
    Z := fun i => Z[i.val]'i.isLt }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

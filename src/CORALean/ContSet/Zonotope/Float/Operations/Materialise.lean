module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.materialise`

Every field is a function type, so the zonotope an operation returns is a closure
over the one it was given, and a loop that iterates operations pays for its whole
history on every entry read. `materialise` stores the four fields; it is the
identity, which `materialise_eq` states and every proof downstream rewrites with,
so what it changes is only what running the definition costs. `Global/Tensor`
says why the vectors are built here rather than by a helper.

`Instances.lean` is where it is applied — an algorithm reaches a representation
through the operation classes and nowhere else, so materialising there bounds
every loop at once without a single operation or guarantee knowing about it.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.materialise (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let c : Vector 𝕋 n := Vector.ofFn Z.c
  let G : Vector (Vector 𝕋 n) Z.h := Vector.ofFn fun j => Vector.ofFn (Z.G j)
  { h := Z.h
    c := fun i => c[i.val]'i.isLt
    G := fun j i => (G[j.val]'j.isLt)[i.val]'i.isLt
    I_error := Z.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

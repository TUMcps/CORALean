module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# `Ellipsoid.materialise`

Every field is a function type, so the ellipsoid an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.materialise (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  let q : Vector 𝕋 n := Vector.ofFn E.c
  let G : Vector (Vector 𝕋 E.k) n := Vector.ofFn fun i => Vector.ofFn fun j => E.G i j
  { k := E.k
    c := fun i => q[i.val]'i.isLt
    G := fun i j => (G[i.val]'i.isLt)[j.val]'j.isLt
    I_error := E.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

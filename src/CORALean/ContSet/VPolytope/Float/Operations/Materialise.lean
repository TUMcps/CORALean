module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.materialise`

Every field is a function type, so the polytope an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here.
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

def VPolytope.materialise (P : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  let V : Vector (Vector 𝕋 n) P.k := Vector.ofFn fun l => Vector.ofFn (P.V l)
  { k := P.k
    V := fun l i => (V[l.val]'l.isLt)[i.val]'i.isLt
    I_error := P.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

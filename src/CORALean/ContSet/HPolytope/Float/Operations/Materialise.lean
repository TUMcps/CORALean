module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# `HPolytope.materialise`

Every field is a function type, so the polytope an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.materialise (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  let A : Vector (Vector 𝕋 n) P.m := Vector.ofFn fun i => Vector.ofFn fun j => P.A i j
  let b : Vector 𝕋 P.m := Vector.ofFn P.b
  let Ae : Vector (Vector 𝕋 n) P.me := Vector.ofFn fun i => Vector.ofFn fun j => P.Ae i j
  let be : Vector 𝕋 P.me := Vector.ofFn P.be
  let b_error : Vector 𝕋 P.m := Vector.ofFn P.b_error
  let be_error : Vector 𝕋 P.me := Vector.ofFn P.be_error
  { m := P.m
    A := fun i j => (A[i.val]'i.isLt)[j.val]'j.isLt
    b := fun i => b[i.val]'i.isLt
    me := P.me
    Ae := fun i j => (Ae[i.val]'i.isLt)[j.val]'j.isLt
    be := fun i => be[i.val]'i.isLt
    b_error := fun i => b_error[i.val]'i.isLt
    be_error := fun i => be_error[i.val]'i.isLt
    I_error := P.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

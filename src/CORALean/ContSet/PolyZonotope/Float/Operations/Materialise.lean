module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.materialise`

Every field is a function type, so the representation an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here.

`E` is stored along with the floats: it is a curried function rather than a
`Mat`, and `compact` reads it through two index maps, so it is where an
unstored exponent matrix costs the most.

## Inputs
* `pZ` – polynomial zonotope

## Output
* the same set with its data stored in vectors
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

def PolyZonotope.materialise (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  let c : Vector 𝕋 n := Vector.ofFn pZ.c
  let G : Vector (Vector 𝕋 n) pZ.h := Vector.ofFn fun l => Vector.ofFn (pZ.G l)
  let E : Vector (Vector ℕ pZ.h) pZ.p := Vector.ofFn fun k => Vector.ofFn fun l => pZ.E k l
  let GI : Vector (Vector 𝕋 n) pZ.q := Vector.ofFn fun j => Vector.ofFn (pZ.GI j)
  { p := pZ.p
    h := pZ.h
    q := pZ.q
    c := fun i => c[i.val]'i.isLt
    G := fun l i => (G[l.val]'l.isLt)[i.val]'i.isLt
    E := fun k l => (E[k.val]'k.isLt)[l.val]'l.isLt
    GI := fun j i => (GI[j.val]'j.isLt)[i.val]'i.isLt
    I_error := pZ.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

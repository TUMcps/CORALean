module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.materialise`

Every field is a function type, so the shadow an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here.

## Inputs
* `S` – spectrahedral shadow

## Output
* `S` with its fields stored as vectors, the same shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.materialise (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let A₀ : Vector (Vector 𝕋 S.k) S.k := Vector.ofFn fun i => Vector.ofFn fun j => S.A₀ i j
  let A : Vector (Vector (Vector 𝕋 S.k) S.k) S.m :=
    Vector.ofFn fun l => Vector.ofFn fun i => Vector.ofFn fun j => S.A l i j
  let c : Vector 𝕋 n := Vector.ofFn S.c
  let G : Vector (Vector 𝕋 n) S.m := Vector.ofFn fun j => Vector.ofFn (S.G j)
  { k := S.k
    m := S.m
    A₀ := fun i j => (A₀[i.val]'i.isLt)[j.val]'j.isLt
    A := fun l i j => ((A[l.val]'l.isLt)[i.val]'i.isLt)[j.val]'j.isLt
    c := fun i => c[i.val]'i.isLt
    G := fun j i => (G[j.val]'j.isLt)[i.val]'i.isLt
    I_error := S.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# `ConPolyZono.materialise`

Every field is a function type, so the representation an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here.
Both exponent matrices are stored along with the floats, being curried functions
rather than `Mat`s.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.materialise (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let c : Vector 𝕋 n := Vector.ofFn cPZ.c
  let G : Vector (Vector 𝕋 n) cPZ.h := Vector.ofFn fun l => Vector.ofFn (cPZ.G l)
  let E : Vector (Vector ℕ cPZ.h) cPZ.p := Vector.ofFn fun k => Vector.ofFn fun l => cPZ.E k l
  let GI : Vector (Vector 𝕋 n) cPZ.qI := Vector.ofFn fun j => Vector.ofFn (cPZ.GI j)
  let A : Vector (Vector 𝕋 cPZ.cons.q) cPZ.cons.m :=
    Vector.ofFn fun i => Vector.ofFn fun l => cPZ.cons.A i l
  let b : Vector 𝕋 cPZ.cons.m := Vector.ofFn cPZ.cons.b
  let b_error : Vector 𝕋 cPZ.cons.m := Vector.ofFn cPZ.cons.b_error
  let R : Vector (Vector ℕ cPZ.cons.q) cPZ.p :=
    Vector.ofFn fun k => Vector.ofFn fun l => cPZ.cons.R k l
  -- every field now reads out of a stored vector, so nothing is left as a closure
  { p := cPZ.p
    h := cPZ.h
    qI := cPZ.qI
    c := fun i => c[i.val]'i.isLt
    G := fun l i => (G[l.val]'l.isLt)[i.val]'i.isLt
    E := fun k l => (E[k.val]'k.isLt)[l.val]'l.isLt
    GI := fun j i => (GI[j.val]'j.isLt)[i.val]'i.isLt
    cons := ⟨cPZ.cons.m, cPZ.cons.q, fun i l => (A[i.val]'i.isLt)[l.val]'l.isLt,
      fun k l => (R[k.val]'k.isLt)[l.val]'l.isLt, fun i => b[i.val]'i.isLt,
      fun i => b_error[i.val]'i.isLt, cPZ.cons.op, cPZ.cons.dom⟩
    cons_eq := cPZ.cons_eq
    cons_dom := cPZ.cons_dom
    I_error := cPZ.I_error.materialise }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

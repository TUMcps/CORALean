import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.mtimes`

CORA's `@conPolyZono/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.

The dimension variables are `k` and `n` rather than the usual `m` and `n`: the
structure already has a field named `m`, and reading the two in one signature is
harder than renaming one of them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {k n : ℕ}

def ConPolyZono.mtimes (M : Mat ℝ k n) (C : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := M *ᵥ C.c
  G := fun i => M *ᵥ C.G i
  E := C.E
  GI := fun j => M *ᵥ C.GI j
  A := C.A
  b := C.b
  EC := C.EC

end CORALean.Real

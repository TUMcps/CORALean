import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.map`

A linear map applies to the centre and to both generator blocks and touches
nothing else — not the exponent matrix, not the counts, and above all not the
constraints.

That last part is the whole content of the file. The constraints live on the
factors, and a map of the ambient space does not move a factor, so the set of
admissible factor vectors is the same before and after. Exactness follows for
the same reason it does for a polynomial zonotope: the same witnesses work in
both directions.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

def ConPolyZono.map (f : α →ₗ[ℝ] β) (C : ConPolyZono α) : ConPolyZono β where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := f C.c
  G := fun i => f (C.G i)
  E := C.E
  GI := fun j => f (C.GI j)
  A := C.A
  b := C.b
  EC := C.EC

end CORALean.Real

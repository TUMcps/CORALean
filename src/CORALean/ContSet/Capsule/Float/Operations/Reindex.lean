module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Interval.Float.Operations.Reindex

@[expose] public section

/-!
# `Capsule.reindex` over a floating-point scalar

CORA's `@capsule/lift_` at a permutation of the coordinates: center and direction composed with
the relabelling, the radius unchanged, the error box relabelled too. The stored floats are moved,
never computed with, so there is nothing to pay.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coordinates read in another order: center, direction and box composed with `e`, radius
kept. -/
def Capsule.reindex (e : Fin m ≃ Fin n) (C : Capsule 𝕋 n) : Capsule 𝕋 m where
  c := fun i => C.c (e i)
  g := fun i => C.g (e i)
  r := C.r
  I_error := C.I_error.reindex e

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

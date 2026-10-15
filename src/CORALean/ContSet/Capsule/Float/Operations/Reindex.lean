module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.reindex` over a floating-point scalar

CORA's `@capsule/lift_` at a permutation of the coordinates: center and direction composed with
the relabelling, the radius unchanged. The stored floats are moved, never computed with, and the
capsule stores its radius rather than an error box, so there is nothing to pay.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coordinates read in another order: center and direction composed with `e`, radius kept. -/
def Capsule.reindex (e : Fin m ≃ Fin n) (C : Capsule 𝕋 n) : Capsule 𝕋 m where
  c := fun i => C.c (e i)
  g := fun i => C.g (e i)
  r := C.r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

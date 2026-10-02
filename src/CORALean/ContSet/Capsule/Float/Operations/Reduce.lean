import CORALean.ContSet.Capsule.Float.Capsule

/-!
# `Capsule.reduce` over a floating-point scalar

CORA's `@capsule/reduce`, whose body is empty and returns its input. Nothing is computed, and the
capsule stores its radius rather than an error box, so there is nothing to pay.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `@capsule/reduce` returns its input: there is no order to reduce to. -/
def Capsule.reduce (C : Capsule 𝕋 n) (_ : ℕ) : Capsule 𝕋 n := C

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

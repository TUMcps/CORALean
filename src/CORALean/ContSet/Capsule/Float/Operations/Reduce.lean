module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.reduce` over a floating-point scalar

CORA's `@capsule/reduce`, whose body is empty and returns its input. Nothing is computed, and the
capsule stores its radius rather than an error box, so there is nothing to pay.

## Inputs
* `C` – capsule
* `_` – target order, unused

## Output
* the capsule itself, unchanged
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `@capsule/reduce` returns its input: there is no order to reduce to. -/
def Capsule.reduce (C : Capsule 𝕋 n) (_ : ℕ) : Capsule 𝕋 n := C

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

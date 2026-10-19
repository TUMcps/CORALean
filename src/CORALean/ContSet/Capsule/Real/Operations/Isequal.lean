module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# `Capsule.isequal`

CORA's `@capsule/isequal.m` for two capsules: center, generator and radius agree to the
tolerance (`abs(.) < tol`, so at `tol = eps` they must be, in effect, equal). Here the tolerance
is `0` and the three fields are equal; the emptiness case CORA tests first (both empty, or
neither) is left to the theorem, since two empty capsules need not have equal fields.

## Inputs
* `C` – first capsule
* `S` – second capsule

## Output
* `Prop` that the fields agree
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule/isequal` at tolerance `0`: center, generator and radius are equal. -/
def Capsule.isequal (C S : Capsule n) : Prop := C.c = S.c ∧ C.g = S.g ∧ C.r = S.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

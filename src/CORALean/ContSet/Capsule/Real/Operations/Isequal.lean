import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.isequal`

CORA's `@capsule/isequal.m` for two capsules: centre, generator and radius agree to the
tolerance (`abs(.) < tol`, so at `tol = eps` they must be, in effect, equal). Here the tolerance
is `0` and the three fields are equal; the emptiness case CORA tests first (both empty, or
neither) is left to the theorem, since two empty capsules need not have equal fields.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule/isequal` at tolerance `0`: centre, generator and radius are equal. -/
def Capsule.isequal (C S : Capsule n) : Prop := C.c = S.c ∧ C.g = S.g ∧ C.r = S.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

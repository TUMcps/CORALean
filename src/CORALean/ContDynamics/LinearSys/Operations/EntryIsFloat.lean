import CORALean.Global.Float.SoundFloatArithmetic

/-!
# One float entry against a constant

`entryIsFloat a x` tests `x` against `a` by `le` in both directions. A float answers `true` for `le`
only when its real value is at most the other's, so a `true` here is a proof that the two real
values are equal and a `false` claims nothing: a one-sided test, as `le` is.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The entry equals `a`, as far as `le` can tell: `a ≤ x` and `x ≤ a`. -/
def LinearSys.entryIsFloat (a x : 𝕋) : Bool := le a x && le x a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

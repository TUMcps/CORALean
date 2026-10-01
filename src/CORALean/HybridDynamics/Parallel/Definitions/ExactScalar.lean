import CORALean.Global.Scalar

/-!
# A scalar whose arithmetic is the real one's

`Scalar` stores a number and reads it back as a real, and nothing more: it has no `0`, no `1`
and no `+`. Assembling a block matrix out of component matrices needs all three, and
the assembled matrix must read back as the block matrix of what the components read back as.
That is this class: the entry-wise reading `toReal`, a homomorphism for the three.

It holds at `ℝ`, and at no rounded scalar: `toReal (a + b)` is `toReal a + toReal b` only
when the sum is exact, so a float automaton assembles its product by other means (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar


-- ========================================  MAIN TYPE  ========================================= --

class ExactScalar (𝕋 : Type) [Scalar 𝕋] extends Zero 𝕋, One 𝕋, Add 𝕋 where
  toReal : 𝕋 → ℝ
  toRealMat_apply {a b : ℕ} (M : Mat 𝕋 a b) (i : Fin a) (j : Fin b) :
    toRealMat M i j = toReal (M i j)
  toRealVec_apply {a : ℕ} (v : Vec 𝕋 a) (i : Fin a) : toRealVec v i = toReal (v i)
  toReal_zero : toReal 0 = 0
  toReal_one : toReal 1 = 1
  toReal_add (a b : 𝕋) : toReal (a + b) = toReal a + toReal b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

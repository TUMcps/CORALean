import Mathlib.Data.Rat.Defs

/-!
# `randverify`: a rational unit vector

`ℓ(t) = ((1 - t²) / (1 + t²), 2t / (1 + t²))` for a rational `t`, the rational parametrisation of
the unit circle (every point but `(-1, 0)`, approached as `t → ±∞`): `‖ℓ(t)‖₂ = 1` exactly. For
`t = a / b` it is returned as an integer vector `p = (b² - a², 2ab)` and its length
`q = a² + b²`, `ℓ = p / q`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def ratUnit (t : ℚ) : (ℤ × ℤ) × ℕ :=
  let a := t.num
  let b : ℤ := t.den
  ((b * b - a * a, 2 * a * b), (a * a + b * b).toNat)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

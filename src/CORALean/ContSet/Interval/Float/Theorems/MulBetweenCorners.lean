import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# A product of two float-bounded factors stays between the four corner products

`mulLo_le`/`le_mulHi` compose with the real fact,
`Real.Interval.mul_between_corners`: `mulLo`/`mulHi` round every corner product
away from the interval before comparing, so the float hull is never inside the
real one.

Eq. (3.1) of [1, Def. 5] for `⊗`, proved here from directed rounding.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A product of two factors, each bounded within a float box, never leaves the
hull of the four corner products, each corner rounded away from the box. -/
theorem Interval.mul_between_corners {a b c d : 𝕋} {y x : ℝ} (hy₁ : toReal a ≤ y)
    (hy₂ : y ≤ toReal b) (hx₁ : toReal c ≤ x) (hx₂ : x ≤ toReal d) :
    toReal (Interval.mulLo a b c d) ≤ y * x ∧ y * x ≤ toReal (Interval.mulHi a b c d) :=
  ⟨le_trans (Interval.mulLo_le a b c d) (Real.Interval.mul_between_corners hy₁ hy₂ hx₁ hx₂).1,
   le_trans (Real.Interval.mul_between_corners hy₁ hy₂ hx₁ hx₂).2 (Interval.le_mulHi a b c d)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

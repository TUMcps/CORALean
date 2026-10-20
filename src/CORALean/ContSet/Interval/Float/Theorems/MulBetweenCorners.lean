module

public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# A product of two float-bounded factors stays between the four corner products

`mulLo_le`/`le_mulHi` compose with the real fact,
`Real.Interval.mul_between_corners`: `mulLo`/`mulHi` round every corner product
away from the interval before comparing, so the float hull is never inside the
real one.

Eq. (3.1) of [1, Def. 5] for `⊗`, proved here from directed rounding.

## Inputs
* `a` – lower end of the first factor
* `b` – upper end of the first factor
* `c` – lower end of the second factor
* `d` – upper end of the second factor
* `y` – real value of the first factor
* `x` – real value of the second factor

## Hypotheses
* `hy₁` – lower end below `y`
* `hy₂` – `y` below the upper end
* `hx₁` – lower end below `x`
* `hx₂` – `x` below the upper end

## Conclusion
* the product `y x` lies between the lower and upper corner products

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

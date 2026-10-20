module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# A float matrix read as reals, times a vector

What `toRealMat` and `Matrix.mulVec` say together: negating a float matrix entrywise negates its
products, since negation is exact, and a row of a stacked matrix reads as the row of the block it
came from.

## Inputs
* `M` – float matrix
* `x` – real vector

## Hypotheses
* none

## Conclusion
* negating the float matrix negates its real product with the vector
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Negation is exact, so the negated rows read the negated products. -/
theorem toRealMat_neg_mulVec (M : Mat 𝕋 m n) (x : Vec ℝ n) :
    toRealMat (-M) *ᵥ x = -(toRealMat M *ᵥ x) := by
  rw [toRealMat_neg, Matrix.neg_mulVec]

/-- A row of the second block of a stacked matrix, read as reals and multiplied, is the block's
own row product. -/
theorem toRealMat_append_mulVec_natAdd {m₁ m₂ : ℕ} (A₁ : Mat 𝕋 m₁ n) (A₂ : Mat 𝕋 m₂ n)
    (x : Vec ℝ n) (j : Fin m₂) :
    (toRealMat (Fin.append A₁ A₂) *ᵥ x) (Fin.natAdd m₁ j) = (toRealMat A₂ *ᵥ x) j := by
  show ∑ k, toReal (Fin.append A₁ A₂ (Fin.natAdd m₁ j) k) * x k = _
  rw [Fin.append_right]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

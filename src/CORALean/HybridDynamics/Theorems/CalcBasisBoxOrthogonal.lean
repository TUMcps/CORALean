module

public import CORALean.HybridDynamics.Operations.CalcBasisBox

@[expose] public section

/-!
# The `'box'` basis is orthogonal

A basis for an enclosure by rotated boxes must be invertible, and an orthogonal one is its own
inverse's transpose; the identity is orthogonal, so the enclosure is the interval hull itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Location

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eye(n)` is `1`, so `B Bᵀ = Bᵀ B = 1`, for the real matrix the stored one denotes. -/
theorem Location.calcBasisBox_orthogonal (n : ℕ) :
    toRealMat (calcBasisBox 𝕋 n) * (toRealMat (calcBasisBox 𝕋 n))ᵀ = 1 ∧
      (toRealMat (calcBasisBox 𝕋 n))ᵀ * toRealMat (calcBasisBox 𝕋 n) = 1 := by -- --- PROOF ---
  -- the stored matrix reads as the identity: `1` on the diagonal, `0` off it
  have h : toRealMat (calcBasisBox 𝕋 n) = 1 := by
    funext i j
    rw [Scalar.toRealMat_apply]
    by_cases hij : i = j
    · subst hij
      simp [Location.calcBasisBox, ExactScalar.toReal_one]
    · simp [Location.calcBasisBox, hij, ExactScalar.toReal_zero, Matrix.one_apply_ne hij]
  -- so both products are `1 * 1ᵀ`
  rw [h]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

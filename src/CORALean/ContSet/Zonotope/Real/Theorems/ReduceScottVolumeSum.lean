module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The volume of `X = {[T v], c}` in terms of `r = T⁻¹v`

[1, Sec. 4.3 (new reduction)]: by the zonotope volume formula of Bravo et al. (2006),
`v(X) = 2ⁿ(|det T| + Σᵢ |det[t₁ ⋯ t_{i-1} v t_{i+1} ⋯ tₙ]|)`, and the paper rewrites the sum
as `= 2ⁿ|det T|(1 + Σᵢ|rᵢ|)`. The formula is Bravo et al.'s, restated. This is the paper's step
after it: replacing column `i` of `T` by `v` multiplies the determinant by `rᵢ`, which is Cramer's
rule, `det[t₁ ⋯ v ⋯ tₙ] = (adj T · v)ᵢ = det T · (T⁻¹v)ᵢ`.

## Inputs
* `n` – dimension
* `T` – basis matrix
* `v` – replacement vector

## Hypotheses
* `hT` – `T` invertible

## Conclusion
* the volume sum equals `2ⁿ |det T|` times a coefficient sum

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: `2ⁿ(|det T| + Σᵢ|det[t₁ ⋯ v ⋯ tₙ]|) = 2ⁿ|det T|(1 + Σᵢ|rᵢ|)`,
`r = T⁻¹v`. -/
theorem Zonotope.reduceScott_volume_sum {n : ℕ} (T : Mat ℝ n n) (hT : T.det ≠ 0)
    (v : Vec ℝ n) : -- --- CONCL ---
    2 ^ n * (|T.det| + ∑ i, |(T.updateCol i v).det|)
      = 2 ^ n * |T.det| * (1 + ∑ i, |(T⁻¹ *ᵥ v) i|) := by -- --- PROOF ---
  -- Cramer's rule: column `i` replaced by `v` scales the determinant by `(T⁻¹v)ᵢ`
  have hcol : ∀ i, (T.updateCol i v).det = T.det * (T⁻¹ *ᵥ v) i := fun i => by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.inv_def,
      Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
      ← mul_assoc, mul_inv_cancel₀ hT, one_mul]
  simp only [hcol, abs_mul, ← Finset.mul_sum]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

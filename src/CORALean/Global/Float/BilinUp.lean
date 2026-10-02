import CORALean.Global.Float.SoundFloatArithmetic
import Mathlib.Data.Matrix.Mul

/-!
# A bilinear form's magnitude, bounded upward

`aᵀ P b` rounded up, for non-negative `a`, `P`, `b` bounding `|v|`, `|M|` and `|w|`
entrywise: `|vᵀ M w| ≤ aᵀ P b`. CORA's `'lin'` Lagrange bound `0.5 * dz' * H_ * dz`
(`priv_abstrerr_lin`) is this at `a = b = |dz|` and `P = max |H|`, and the
polynomialization's cross terms are it at two different vectors.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aᵀ P b`, each product and each sum rounded up. -/
def bilinUp (a : Vec 𝕋 d) (P : Mat 𝕋 d d) (b : Vec 𝕋 d) : 𝕋 := dotUp a (mulVecUp P b)

/-- Entrywise bounds on the magnitudes bound the form's. -/
theorem abs_bilin_le_bilinUp [SoundFloatArithmetic 𝕋] {a b : Vec 𝕋 d} {P : Mat 𝕋 d d}
    {v w : Vec ℝ d} {M : Mat ℝ d d} (hv : ∀ j, |v j| ≤ toReal (a j))
    (hw : ∀ k, |w k| ≤ toReal (b k)) (hM : ∀ j k, |M j k| ≤ toReal (P j k)) :
    |v ⬝ᵥ (M *ᵥ w)| ≤ toReal (bilinUp a P b) := by -- --- PROOF ---
  -- the inner sums first: `|(M w)ⱼ| ≤ (P b)ⱼ`, rounded up
  have hrow : ∀ j, |(M *ᵥ w) j| ≤ toReal (mulVecUp P b j) := fun j =>
    calc |(M *ᵥ w) j| = |∑ k, M j k * w k| := rfl
      _ ≤ ∑ k, |M j k * w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, toReal (P j k) * toReal (b k) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hM j k) (hw k) (abs_nonneg _) (le_trans (abs_nonneg _) (hM j k))
      _ ≤ toReal (mulVecUp P b j) := le_dotUp _ _
  -- then the outer one, `a` non-negative because it bounds a magnitude
  calc |v ⬝ᵥ (M *ᵥ w)| = |∑ j, v j * (M *ᵥ w) j| := rfl
    _ ≤ ∑ j, |v j * (M *ᵥ w) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, toReal (a j) * toReal (mulVecUp P b j) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hv j) (hrow j) (abs_nonneg _) (le_trans (abs_nonneg _) (hv j))
    _ ≤ toReal (bilinUp a P b) := le_dotUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.Interval.Float.Theorems.AbsMulVecLeDotUp
import Mathlib.Data.Matrix.Basic

/-!
# A matrix of an interval matrix applied to a bounded vector

Every matrix `A` of `M` has `|A i k| ≤ magnitudeMat M i k`, so a vector `x` with `|x k| ≤ ξ k`
has `|(A x) i| ≤ dotUp (magnitudeMat M i) ξ`, the products and the sum rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.abs_mulVec_le_magnitudeMat {M : Interval (Mat 𝕋 m n)} {A : Mat ℝ m n}
    (hA : A ∈ M.construct) {x : Vec ℝ n} {ξ : Vec 𝕋 n} (hx : ∀ k, |x k| ≤ toReal (ξ k))
    (i : Fin m) :
    |((A *ᵥ x) i)| ≤ toReal (dotUp (M.magnitudeMat i) ξ) :=
  abs_mulVec_le_dotUp (fun i k => by
    have hk := Interval.mem_mat_iff.mp hA i k
    rw [Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hk.1 hk.2) hx i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

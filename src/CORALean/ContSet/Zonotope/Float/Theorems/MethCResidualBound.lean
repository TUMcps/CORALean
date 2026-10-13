import CORALean.ContSet.Zonotope.Float.Operations.MethCResidual
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `methCResidual` bounds `|1 - H P|`

Each entry of `H P` lies between its two directed dot products, so `1 - (H P)ᵢⱼ` lies between
the two differences, and `methCResidual` takes the larger magnitude of their bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.methCResidual_bound (H P : Mat 𝕋 n n) (i j : Fin n) :
    |(1 - toRealMat H * toRealMat P) i j|
      ≤ toReal (Zonotope.methCResidual H P i j) := by -- --- PROOF ---
  -- the entry of the product, between its two directed dot products
  have hd := dotDown_le (H i) fun l => P l j
  have hu := le_dotUp (H i) fun l => P l j
  have hprod : (toRealMat H * toRealMat P) i j
      = ∑ l, toReal (H i l) * toReal (P l j) := rfl
  have hδ : toReal (if i = j then (one : 𝕋) else zero) = if i = j then (1 : ℝ) else 0 := by
    split_ifs
    · exact toReal_one
    · exact toReal_zero
  have hsub : (1 - toRealMat H * toRealMat P) i j
      = (if i = j then (1 : ℝ) else 0) - ∑ l, toReal (H i l) * toReal (P l j) := by
    rw [Matrix.sub_apply, hprod, Matrix.one_apply]
  have h1 := subDown_le_sub (if i = j then (one : 𝕋) else zero) (dotUp (H i) fun l => P l j)
  have h2 := sub_le_subUp (if i = j then (one : 𝕋) else zero) (dotDown (H i) fun l => P l j)
  rw [hδ] at h1 h2
  rw [hsub]
  simp only [Zonotope.methCResidual, toReal_maximum, toReal_absolute]
  exact abs_le_max_abs_abs (by linarith) (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

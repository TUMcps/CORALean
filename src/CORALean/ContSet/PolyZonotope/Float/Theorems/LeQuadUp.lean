import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap

/-!
# A directed sum of per-term maxima never undershoots a bilinear value
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_le_max_mul {a lo hi w : ℝ} (h1 : lo ≤ w) (h2 : w ≤ hi) :
    a * w ≤ max (a * lo) (a * hi) := by -- --- PROOF ---
  rcases le_total 0 a with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_max_left _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.le_quadUp {g wlo whi : Vec 𝕋 n} {w : Vec ℝ n}
    (hw : ∀ r, toReal (wlo r) ≤ w r ∧ w r ≤ toReal (whi r)) :
    (∑ r, toReal (g r) * w r) ≤ toReal (PolyZonotope.quadUp g wlo whi) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun r _ => ?_) (sum_le_sumUp _)
  rw [toReal_maximum]
  exact le_trans (PolyZonotope.aux_le_max_mul (hw r).1 (hw r).2)
    (max_le_max (mul_le_mulUp _ _) (mul_le_mulUp _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

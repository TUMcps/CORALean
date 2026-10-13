import CORALean.ContSet.HPolytope.Float.Operations.RowScale

/-!
# A row scale is positive

The quotient `1 / ‖Aᵢ‖₂` is taken only at a norm certified positive, and rounded up, so it is
above a positive number; otherwise the scale is `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.rowScale_pos (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.m) :
    0 < toReal (P.rowScale p i) := by -- --- PROOF ---
  by_cases h : ltStrict zero (normUp p (P.A i)) = true
  · simp only [HPolytope.rowScale, h, if_true]
    have hpos := toReal_lt_of_ltStrict h
    rw [toReal_zero] at hpos
    refine lt_of_lt_of_le ?_ (div_le_divUp _ _ hpos)
    rw [toReal_one]
    exact one_div_pos.mpr hpos
  · simp only [HPolytope.rowScale, h, if_false, Bool.false_eq_true]
    rw [toReal_one]
    exact one_pos

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

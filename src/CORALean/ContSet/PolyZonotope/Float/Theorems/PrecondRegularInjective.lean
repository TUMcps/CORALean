import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.MulVecInjectiveOfResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.PrecondRegular

/-!
# `precondRegular` certifies an injective preconditioner

`M C` lies between its two roundings, so `|(1 - M C)ᵢⱼ|` is at most the larger of the two
roundings' distances from `1ᵢⱼ`, and a row of those summing below `1` gives
`mulVec_injective_of_residual`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.precondRegular_injective {M C : Mat 𝕋 n n}
    (h : PolyZonotope.precondRegular M C = true) :
    Function.Injective (toRealMat C).mulVec := by -- --- PROOF ---
  refine mulVec_injective_of_residual (toRealMat M) (toRealMat C) fun i => ?_
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_eq (toReal_lt_of_ltStrict hi) (toReal_one (𝕋 := 𝕋)))
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  -- the entry of `M C` between its roundings, and `1ᵢⱼ` read exactly
  have hlo : toReal (matMulDown M C i j) ≤ (toRealMat M * toRealMat C) i j := dotDown_le _ _
  have hhi : (toRealMat M * toRealMat C) i j ≤ toReal (matMulUp M C i j) := le_dotUp _ _
  have hδ : toReal (if i = j then (one : 𝕋) else zero) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    by_cases hij : i = j
    · rw [if_pos hij, hij, Matrix.one_apply_eq, toReal_one]
    · rw [if_neg hij, Matrix.one_apply_ne hij, toReal_zero]
  rw [toReal_maximum, toReal_absolute, toReal_absolute, Matrix.sub_apply]
  refine abs_le_max_abs_abs ?_ ?_
  · exact le_trans (subDown_le_sub _ _) (by rw [hδ]; linarith)
  · exact le_trans (by rw [hδ]; linarith) (sub_le_subUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

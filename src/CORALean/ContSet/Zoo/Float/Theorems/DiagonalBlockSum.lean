import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# Only the diagonal entry reaches a coordinate

In the box's float zonotope, whose generator block is diagonal, coordinate `i` is reached only by
generator `i`.
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

theorem Zoo.diagonalBlock_sum (I : Interval (Vec 𝕋 n)) (i : Fin n) (t : Vec ℝ n) :
    ∑ j : Fin n, toReal (diagonalBlock I.radiusFrom i j) * t j
      = toReal (I.radiusFrom i) * t i := by -- --- PROOF ---
  rw [Finset.sum_eq_single i]
  · simp [toReal_diagonalBlock, Matrix.diagonal_apply_eq, toRealVec]
  · intro j _ hj
    simp [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

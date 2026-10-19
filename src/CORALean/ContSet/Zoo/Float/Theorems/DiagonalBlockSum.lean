module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# Only the diagonal entry reaches a coordinate

In the box's float zonotope, whose generator block is diagonal, coordinate `i` is reached only by
generator `i`.

## Inputs
* `I` – box
* `i` – coordinate index
* `t` – real point

## Hypotheses
* none

## Conclusion
* only the diagonal generator reaches coordinate `i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.diagonalBlock_sum (I : Interval (Vec 𝕋 n)) (i : Fin n) (t : Vec ℝ n) :
    ∑ j : Fin n, toReal (diagonalBlock I.radiusFrom j i) * t j
      = toReal (I.radiusFrom i) * t i := by -- --- PROOF ---
  rw [Finset.sum_eq_single i]
  · simp [toReal_diagonalBlock, Matrix.diagonal_apply_eq, toRealVec]
  · intro j _ hj
    simp [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ hj]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Zonotope.Float.Operations.RightInvQ
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `rightInvQ` bounds every absolute row sum of `1 - G H`

Each entry is bounded by `aux_rightInvResidual`, a row of them is summed upward, and the largest of
the sums is taken exactly.

## Inputs
* `G` – generator matrix
* `H` – candidate right inverse
* `i` – row index

## Hypotheses
* none

## Conclusion
* absolute row sum of the residual is bounded
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_rightInvResidual_bound (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) (i j : Fin n) :
    |((1 : Mat ℝ n n) - toRealMat G * toRealMat H) i j|
      ≤ toReal (Zonotope.aux_rightInvResidual G H i j) := by -- --- PROOF ---
  have hd := dotDown_le (fun l => G i l) fun l => H l j
  have hu := le_dotUp (fun l => G i l) fun l => H l j
  have hprod : (toRealMat G * toRealMat H) i j
      = ∑ l, toReal (G i l) * toReal (H l j) := rfl
  have hδ : toReal (if i = j then (one : 𝕋) else zero) = if i = j then (1 : ℝ) else 0 := by
    split_ifs
    · exact toReal_one
    · exact toReal_zero
  have hsub : ((1 : Mat ℝ n n) - toRealMat G * toRealMat H) i j
      = (if i = j then (1 : ℝ) else 0) - ∑ l, toReal (G i l) * toReal (H l j) := by
    rw [Matrix.sub_apply, hprod, Matrix.one_apply]
  have h1 := subDown_le_sub (if i = j then (one : 𝕋) else zero)
    (dotUp (fun l => G i l) fun l => H l j)
  have h2 := sub_le_subUp (if i = j then (one : 𝕋) else zero)
    (dotDown (fun l => G i l) fun l => H l j)
  rw [hδ] at h1 h2
  rw [hsub]
  simp only [Zonotope.aux_rightInvResidual, toReal_maximum, toReal_absolute]
  exact abs_le_max_abs_abs (by linarith) (by linarith)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.rightInvQ_bound (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) (i : Fin n) :
    ∑ j, |((1 : Mat ℝ n n) - toRealMat G * toRealMat H) i j|
      ≤ toReal (Zonotope.rightInvQ G H) := by
  refine le_trans (Finset.sum_le_sum fun j _ => Zonotope.aux_rightInvResidual_bound G H i j) ?_
  refine le_trans (sum_le_sumUp fun j => Zonotope.aux_rightInvResidual G H i j) ?_
  exact le_maximumOver (fun i => sumUp fun j => Zonotope.aux_rightInvResidual G H i j) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

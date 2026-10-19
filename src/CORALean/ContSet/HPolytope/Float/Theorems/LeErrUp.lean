module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# What a row reads on the error box, at most

A linear function of one coordinate is largest at one end of the coordinate's range, so each
term of `a · e` is bounded by the end the sign of `aⱼ` picks, and `errUp` sums those bounds
upward. This is how every operation that moves the box into the rows (`absorbRounding`,
`boxToSlack`) bounds what a box point adds to a row.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The most the row `a` reads on the error box: a linear function of one coordinate is largest
at one end of its range, so each term is bounded by the end its sign picks, and the terms are
summed upward. -/
theorem HPolytope.le_errUp (P : HPolytope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) {e : Vec ℝ n}
    (he : e ∈ P.I_error.construct) :
    ∑ j, toReal (a j) * e j ≤ toReal (P.errUp a) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  have hlo : toReal (P.I_error.inf j) ≤ e j := (he j).1
  have hhi : e j ≤ toReal (P.I_error.sup j) := (he j).2
  rw [toReal_maximum]
  rcases le_total 0 (toReal (a j)) with hs | hs
  · refine le_trans ?_ (le_max_left _ _)
    exact le_trans (mul_le_mul_of_nonneg_left hhi hs) (mul_le_mulUp _ _)
  · refine le_trans ?_ (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonpos_left hlo hs) (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

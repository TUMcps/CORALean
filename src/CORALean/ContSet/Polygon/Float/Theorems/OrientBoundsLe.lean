module

public import CORALean.ContSet.Polygon.Float.Operations.OrientBounds

@[expose] public section

/-!
# `Polygon.orientBounds` brackets the orientation

Each of the six products lies between its two roundings, and the rounded sums bracket the sums,
so the orientation of the points read as reals lies between the two stored bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.orientBounds_le (p q r : Vec 𝕋 2) : -- --- STMT ---
    toReal (Polygon.orientBounds p q r).inf
        ≤ (toReal (q 0) - toReal (p 0)) * (toReal (r 1) - toReal (p 1))
          - (toReal (q 1) - toReal (p 1)) * (toReal (r 0) - toReal (p 0))
      ∧ (toReal (q 0) - toReal (p 0)) * (toReal (r 1) - toReal (p 1))
          - (toReal (q 1) - toReal (p 1)) * (toReal (r 0) - toReal (p 0))
        ≤ toReal (Polygon.orientBounds p q r).sup := by -- --- PROOF ---
  -- the two bracketing sums, written out term by term
  have lo := sumDown_le_sum ![mulDown (q 0) (r 1), mulDown (p 0) (q 1), mulDown (r 0) (p 1),
    neg (mulUp (q 0) (p 1)), neg (mulUp (p 0) (r 1)), neg (mulUp (r 0) (q 1))]
  have hi := sum_le_sumUp ![mulUp (q 0) (r 1), mulUp (p 0) (q 1), mulUp (r 0) (p 1),
    neg (mulDown (q 0) (p 1)), neg (mulDown (p 0) (r 1)), neg (mulDown (r 0) (q 1))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    toReal_neg, add_zero] at lo hi
  -- each product between its two roundings
  have m₁ := mulDown_le_mul (q 0) (r 1)
  have m₂ := mulDown_le_mul (p 0) (q 1)
  have m₃ := mulDown_le_mul (r 0) (p 1)
  have m₄ := mulDown_le_mul (q 0) (p 1)
  have m₅ := mulDown_le_mul (p 0) (r 1)
  have m₆ := mulDown_le_mul (r 0) (q 1)
  have n₁ := mul_le_mulUp (q 0) (r 1)
  have n₂ := mul_le_mulUp (p 0) (q 1)
  have n₃ := mul_le_mulUp (r 0) (p 1)
  have n₄ := mul_le_mulUp (q 0) (p 1)
  have n₅ := mul_le_mulUp (p 0) (r 1)
  have n₆ := mul_le_mulUp (r 0) (q 1)
  -- the orientation is the signed sum of the six products
  have e : (toReal (q 0) - toReal (p 0)) * (toReal (r 1) - toReal (p 1))
      - (toReal (q 1) - toReal (p 1)) * (toReal (r 0) - toReal (p 0))
      = toReal (q 0) * toReal (r 1) + toReal (p 0) * toReal (q 1) + toReal (r 0) * toReal (p 1)
        - toReal (q 0) * toReal (p 1) - toReal (p 0) * toReal (r 1)
        - toReal (r 0) * toReal (q 1) := by ring
  simp only [Polygon.orientBounds]
  rw [e]
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

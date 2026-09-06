import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# A masked sum of stored floats reads back to the exact layer's fibre sum

Outside the fibre every summand is `zero`, which reads as `0`, so the masked
sum's read-back is the fibre sum. What both directed bracketing sums need, one
rounding down and the other up.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The masked sum is the fibre sum: outside the fibre every summand is `zero`,
which reads as `0`. -/
theorem PolyZonotope.sum_mask (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    (∑ l, toReal (if r l = j then G i l else zero))
      = Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j := by
  rw [Real.PolyZonotope.fiberSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : r l = j
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

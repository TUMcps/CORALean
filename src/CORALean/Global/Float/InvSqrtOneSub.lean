module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `(√(1 - c²))⁻¹` rounded in either direction

The factor the derivatives of `arcsin` and `arccos` carry. From above `1 / √(1 - c²)` is rounded
up with the root rounded down, which needs that root positive (`div_le_divUp`'s one partial
guarantee); from below, with the root rounded up, floored at zero. The hypothesis, the rounded
root positive, is what puts `c` strictly inside `(-1, 1)`. `q` is the precision of the root.

## Inputs
* `q` – precision of the root
* `c` – float argument

## Output
* a lower bound of the reciprocal root of one minus the argument squared
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def invSqrtOneSubLo (q : ℕ) (c : 𝕋) : 𝕋 :=
  maximum zero (divDown one (sqrtUp q (subUp one (mulDown c c))))

/-- The upper bound of `1/√(1 - c²)`: the root rounded down, the quotient rounded up. -/
def invSqrtOneSubHi (q : ℕ) (c : 𝕋) : 𝕋 :=
  divUp one (sqrtDown q (subDown one (mulUp c c)))

/-- When the rounded-down root is positive, `|c| < 1` and `invSqrtOneSubLo`, `invSqrtOneSubHi`
enclose `1/√(1 - c²)`. -/
theorem invSqrtOneSub_mem [SoundFloatArithmetic 𝕋] (q : ℕ) (c : 𝕋)
    (h : 0 < toReal (sqrtDown q (subDown one (mulUp c c)))) : -- --- CONCL ---
    toReal c ^ 2 < 1 ∧ 0 ≤ toReal (invSqrtOneSubLo q c) ∧
      toReal (invSqrtOneSubLo q c) ≤ (√(1 - toReal c ^ 2))⁻¹ ∧
      (√(1 - toReal c ^ 2))⁻¹ ≤ toReal (invSqrtOneSubHi q c) := by -- --- PROOF ---
  -- the rounded root below the real one, so positive means `c² < 1`
  have hm1 := mul_le_mulUp c c
  have hm2 := mulDown_le_mul c c
  have ha1 : toReal (subDown one (mulUp c c)) ≤ 1 - toReal c ^ 2 := by
    have := subDown_le_sub (one : 𝕋) (mulUp c c)
    rw [toReal_one] at this; nlinarith
  have hd := le_trans (sqrtDown_le q (subDown one (mulUp c c))) (Real.sqrt_le_sqrt ha1)
  have hs : 0 < √(1 - toReal c ^ 2) := lt_of_lt_of_le h hd
  have h1 : 0 < 1 - toReal c ^ 2 := Real.sqrt_pos.1 hs
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [invSqrtOneSubLo, toReal_maximum, toReal_zero]; exact le_max_left _ _
-- the lower rounding below the real value
  · rw [invSqrtOneSubLo, toReal_maximum, toReal_zero]
    refine max_le (inv_nonneg.2 hs.le) ?_
    have ha2 : 1 - toReal c ^ 2 ≤ toReal (subUp one (mulDown c c)) := by
      have := sub_le_subUp (one : 𝕋) (mulDown c c)
      rw [toReal_one] at this; nlinarith
    have hu := le_trans (Real.sqrt_le_sqrt ha2) (le_sqrtUp q (subUp one (mulDown c c)))
    have hup : 0 < toReal (sqrtUp q (subUp one (mulDown c c))) := lt_of_lt_of_le hs hu
    have := divDown_le_div (one : 𝕋) _ hup
    rw [toReal_one] at this
    refine le_trans this ?_
    simp only [← one_div]
    exact one_div_le_one_div_of_le hs hu
-- the upper rounding above the real value
  · have := div_le_divUp (one : 𝕋) _ h
    rw [toReal_one] at this
    refine le_trans ?_ this
    simp only [← one_div]
    exact one_div_le_one_div_of_le h hd

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

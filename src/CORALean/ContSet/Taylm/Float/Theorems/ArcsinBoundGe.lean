import CORALean.ContSet.Taylm.Float.Operations.ArcsinBound
import CORALean.ContSet.Interval.Float.Theorems.EvalListMem
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.arcsinBound` bounds the derivative of `arcsin`

`abs_iteratedDeriv_asin_le` bounds `|arcsin⁽ᴺ⁺¹⁾|` on `|x| ≤ m < 1` by `asinDom N (m)` times
`(√(1 - m²))⁻⁽²ᴺ⁺¹⁾`; the polynomial is below its `Interval.evalList` enclosure, the power below
`powUp` of the rounded-up `invSqrtOneSubHi`, and the product below its rounding. `hm` is the
rounded root positive at `m`, which puts `m` below one.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Polynomial

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.arcsinBound_ge (q : ℕ) (m : 𝕋)
    (hm : 0 < toReal (sqrtDown q (subDown one (mulUp m m)))) (N : ℕ) {x : ℝ}
    (hx : |x| ≤ toReal m) :
    |iteratedDeriv (N + 1) Real.arcsin x| ≤ toReal (Taylm.arcsinBound q m N) := by -- --- PROOF ---
  -- the magnitude is below one, and `asinDom` as the integer list
  have hv := invSqrtOneSub_mem q m hm
  have hM0 : 0 ≤ toReal m := le_trans (abs_nonneg _) hx
  have hM1 : toReal m < 1 := by nlinarith [hv.1]
  have hDm : ∀ j x, (asinDom j).eval x =
      evalL (recL [1, 0, 1] (fun j => 2 * (j : ℤ) + 1) j) x := fun j x =>
    eval_recL (Q := 1 + X ^ 2) (fun x => by simp [evalL]; ring) _ asinDom rfl
      (fun j => by rw [asinDom]; push_cast; rfl) j x
  -- the derivative below `asinDom N (m)` times the power, each factor then below its rounding
  have h1 := abs_iteratedDeriv_asin_le N hx hM1
  rw [hDm] at h1
  have hU := (Interval.evalList_mem (lo := m) (hi := m) (x := toReal m) le_rfl le_rfl
    (recL [1, 0, 1] (fun j => 2 * (j : ℤ) + 1) N)).2
  have hb : 0 < ((√(1 - toReal m ^ 2))⁻¹) ^ (2 * N + 1) :=
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (by nlinarith))) _
  -- the polynomial is non-negative, being above an absolute value over a positive power
  have ha : 0 ≤ evalL (recL [1, 0, 1] (fun j => 2 * (j : ℤ) + 1) N) (toReal m) := by
    by_contra hneg
    replace hneg := not_le.1 hneg
    have := mul_neg_of_neg_of_pos hneg hb
    linarith [abs_nonneg (iteratedDeriv (N + 1) Real.arcsin x)]
  have hph := le_powUp (inv_nonneg.2 (Real.sqrt_nonneg _)) hv.2.2.2 (2 * N + 1)
  refine le_trans h1 (le_trans ?_ (mul_le_mulUp _ _))
  exact mul_le_mul hU hph hb.le (le_trans ha hU)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

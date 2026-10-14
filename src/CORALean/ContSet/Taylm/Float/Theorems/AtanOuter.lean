module

public import CORALean.ContSet.Taylm.Float.Operations.Atan
public import CORALean.ContSet.Taylm.Float.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Float.Theorems.AbsLeMagUp
public import CORALean.ContSet.Interval.Float.Theorems.EvalListMem
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.atan` encloses `atan ∘ f`

No domain condition: `atan` is smooth on `ℝ`. `Taylm.taylor_outer` at `arctan`, whose derivatives at
the centre are `atanPoly j c · wʲ⁺¹` (`iteratedDeriv_atan`), the polynomial the integer list
`recL` evaluates (`eval_recL`), `Interval.evalList_mem` enclosing it, and whose `(N+1)`-th is
bounded by `atanDom N` at the magnitude (`abs_iteratedDeriv_atan_le`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Polynomial

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.atan_outer (p q : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.atan p q).Encloses fun t => Real.arctan (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  -- the two polynomial sequences as integer lists
  have hP : ∀ j x, (atanPoly j).eval x =
      evalL (recL [1, 0, 1] (fun j => -(2 * ((j : ℤ) + 1))) j) x := fun j x =>
    eval_recL (Q := 1 + X ^ 2) (fun x => by simp [evalL]; ring) _ atanPoly rfl
      (fun j => by rw [atanPoly]; push_cast; rw [sub_eq_add_neg, map_neg, neg_mul]) j x
  have hDm : ∀ j x, (atanDom j).eval x =
      evalL (recL [1, 0, 1] (fun j => 2 * ((j : ℤ) + 1)) j) x := fun j x =>
    eval_recL (Q := 1 + X ^ 2) (fun x => by simp [evalL]; ring) _ atanDom rfl
      (fun j => by rw [atanDom]; push_cast; rfl) j x
  -- `w = (1 + c²)⁻¹` between its roundings
  have hcc : 0 ≤ toReal c * toReal c := mul_self_nonneg _
  have hwl : toReal (maximum zero (divDown one (addUp one (mulUp c c)))) ≤
      ((1 + toReal c ^ 2)⁻¹) := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (by positivity) ?_
    have h1 := add_le_addUp (one : 𝕋) (mulUp c c)
    have h2 := mul_le_mulUp c c
    rw [toReal_one] at h1
    have hpos : 0 < toReal (addUp one (mulUp c c)) := by nlinarith
    have := divDown_le_div (one : 𝕋) (addUp one (mulUp c c)) hpos
    rw [toReal_one] at this
    refine le_trans this ?_
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  -- the upper rounding of `w`
  have hwh : (1 + toReal c ^ 2)⁻¹ ≤
      toReal (divUp one (maximum one (addDown one (mulDown c c)))) := by
    rw [← one_div]
    refine one_div_le_divUp (d := maximum one (addDown one (mulDown c c))) ?_ ?_
    · rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    · rw [toReal_maximum, toReal_one]
      have h1 := addDown_le_add (one : 𝕋) (mulDown c c)
      have h2 := mulDown_le_mul c c
      rw [toReal_one] at h1
      exact max_le (by nlinarith) (by nlinarith)
  have hw0 : (0 : ℝ) ≤ toReal (maximum zero (divDown one (addUp one (mulUp c c)))) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hwpos : (0 : ℝ) ≤ (1 + toReal c ^ 2)⁻¹ := by positivity
  -- the three obligations of `Taylm.taylor_outer`: coefficients, smoothness, derivative bound
  refine Taylm.taylor_outer h Real.arctan c _ _ _
    (evalL (recL [1, 0, 1] (fun j => 2 * ((j : ℤ) + 1)) N) (toReal T.magUp)) ?_
    (fun ξ _ => Real.contDiff_arctan.contDiffAt) (fun ξ hξ => ?_) ?_
  · intro k _
    rcases k with _ | j
    · exact ⟨by simpa using atanDown_le p q c, by simpa using le_atanUp p q c⟩
    · simp only
      -- the polynomial, the power and the factorial between their enclosures
      have hb := Interval.evalList_mem (lo := c) (hi := c) (x := toReal c) le_rfl le_rfl
        (recL [1, 0, 1] (fun j => -(2 * ((j : ℤ) + 1))) j)
      have hG := divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
        (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (j + 1)
      have hpl := powDown_le hw0 hwl (j + 1)
      have hph := le_powUp hwpos hwh (j + 1)
      have hW := Real.Interval.mul_between_corners hpl hph (hG.1) (hG.2)
      have hW' := Real.Interval.mul_between_corners hb.1 hb.2
        (le_trans (Interval.mulLo_le _ _ _ _) hW.1) (le_trans hW.2 (Interval.le_mulHi _ _ _ _))
      -- the derivative as polynomial times power, and the product between the corner products
      rw [iteratedDeriv_atan, hP]
      have : evalL (recL [1, 0, 1] (fun j => -(2 * ((j : ℤ) + 1))) j) (toReal c) *
          (((1 + toReal c ^ 2)⁻¹) ^ (j + 1) * (1 / ((j + 1).factorial : ℝ))) =
          evalL (recL [1, 0, 1] (fun j => -(2 * ((j : ℤ) + 1))) j) (toReal c) *
            ((1 + toReal c ^ 2)⁻¹) ^ (j + 1) / ((j + 1).factorial : ℝ) := by ring
      rw [this] at hW'
      exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hW'.1, le_trans hW'.2 (Interval.le_mulHi _ _ _ _)⟩
-- the derivative bound `atanDom N` at the magnitude
  · rw [← hDm]
    exact abs_iteratedDeriv_atan_le N (T.abs_le_magUp hξ)
  · exact (Interval.evalList_mem (lo := T.magUp) (hi := T.magUp) le_rfl le_rfl _).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

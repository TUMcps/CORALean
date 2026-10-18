module

public import CORALean.ContSet.Taylm.Float.Operations.ArcsinCoef
public import CORALean.ContSet.Interval.Float.Theorems.EvalListMem
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.arcsinCoef` encloses the coefficient of `arcsin`

`arcsin⁽ʲ⁺¹⁾ c / (j+1)!` is `asinPoly j c · v²ʲ⁺¹ · (1 / (j+1)!)` (`iteratedDeriv_inv_sqrt`), the
integer list evaluating as `asinPoly` (`eval_recL`), `Interval.evalList_mem` enclosing it, and
the powers and the factorial between their roundings. `h` is the rounded root positive, which puts
`c` inside `(-1, 1)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Polynomial

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.arcsinCoef_mem (q : ℕ) (c : 𝕋)
    (h : 0 < toReal (sqrtDown q (subDown one (mulUp c c)))) (j : ℕ) : -- --- STMT ---
    toReal (Taylm.arcsinCoef q c j).inf ≤
        iteratedDeriv (j + 1) Real.arcsin (toReal c) / ((j + 1).factorial : ℝ) ∧
      iteratedDeriv (j + 1) Real.arcsin (toReal c) / ((j + 1).factorial : ℝ) ≤
        toReal (Taylm.arcsinCoef q c j).sup := by -- --- PROOF ---
  -- `c` inside `(-1, 1)`, and `asinPoly` as the integer list
  have hv := invSqrtOneSub_mem q c h
  have hP : ∀ j x, (asinPoly j).eval x =
      evalL (recL [1, 0, -1] (fun j => 2 * (j : ℤ) + 1) j) x := fun j x =>
    eval_recL (Q := 1 - X ^ 2) (fun x => by simp [evalL]; ring) _ asinPoly rfl
      (fun j => by rw [asinPoly]; push_cast; rfl) j x
  have hcI : toReal c ∈ Set.Ioo (-1 : ℝ) 1 := by
    have := hv.1
    constructor <;> nlinarith
  -- the three factors between their enclosures
  have hb := Interval.evalList_mem (lo := c) (hi := c) (x := toReal c) le_rfl le_rfl
    (recL [1, 0, -1] (fun j => 2 * (j : ℤ) + 1) j)
  have hG := divFact_mem ⟨(one : 𝕋), (one : 𝕋)⟩ zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (j + 1)
  have hpl := powDown_le hv.2.1 hv.2.2.1 (2 * j + 1)
  have hph := le_powUp (inv_nonneg.2 (Real.sqrt_nonneg _)) hv.2.2.2 (2 * j + 1)
  have hW := Real.Interval.mul_between_corners hpl hph (hG.1) (hG.2)
  have hW' := Real.Interval.mul_between_corners hb.1 hb.2
    (le_trans (Interval.mulLo_le _ _ _ _) hW.1) (le_trans hW.2 (Interval.le_mulHi _ _ _ _))
  -- the derivative as polynomial times power, and the product between the corner products
  have hd : iteratedDeriv (j + 1) Real.arcsin (toReal c) =
      (asinPoly j).eval (toReal c) * ((√(1 - toReal c ^ 2))⁻¹) ^ (2 * j + 1) := by
    rw [iteratedDeriv_succ', Real.deriv_arcsin]
    simp only [one_div]
    exact iteratedDeriv_inv_sqrt j _ hcI
  rw [hd, hP]
  have : evalL (recL [1, 0, -1] (fun j => 2 * (j : ℤ) + 1) j) (toReal c) *
      (((√(1 - toReal c ^ 2))⁻¹) ^ (2 * j + 1) * (1 / ((j + 1).factorial : ℝ))) =
      evalL (recL [1, 0, -1] (fun j => 2 * (j : ℤ) + 1) j) (toReal c) *
        ((√(1 - toReal c ^ 2))⁻¹) ^ (2 * j + 1) / ((j + 1).factorial : ℝ) := by ring
  rw [this] at hW'
  exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hW'.1, le_trans hW'.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

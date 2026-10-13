import CORALean.ContSet.Taylm.Float.Operations.ProdBounds
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

/-!
# `Taylm.prodBounds` brackets the product

A product of factors each in its interval lies in the stored range, the corner products bracketing
each step.
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

theorem Taylm.prodBounds_mem : ∀ {m : ℕ} (f : Fin m → 𝕋 × 𝕋) (x : Fin m → ℝ),
    (∀ i, toReal (f i).1 ≤ x i ∧ x i ≤ toReal (f i).2) →
      toReal (Taylm.prodBounds f).1 ≤ ∏ i, x i ∧
        ∏ i, x i ≤ toReal (Taylm.prodBounds f).2 := by -- --- PROOF ---
  -- no factors: the point `1`
  intro m
  induction m with
  | zero =>
    intro f x _
    simp only [Taylm.prodBounds, Finset.univ_eq_empty, Finset.prod_empty, toReal_one]
    exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    -- the first factor times the product of the others
    intro f x hx
    have hrest := ih (fun i => f i.succ) (fun i => x i.succ) fun i => hx i.succ
    rw [Fin.prod_univ_succ]
    exact Interval.mul_between_corners (hx 0).1 (hx 0).2 hrest.1 hrest.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

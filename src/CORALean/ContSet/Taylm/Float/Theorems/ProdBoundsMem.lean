module

public import CORALean.ContSet.Taylm.Float.Operations.ProdBounds
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Taylm.prodBounds` brackets the product

A product of factors each in its interval lies in the stored range, the corner products bracketing
each step.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the product of values in their brackets lies in the product bracket
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.prodBounds_mem : -- --- CONCL ---
    ∀ {m : ℕ} (f : Fin m → Interval 𝕋) (x : Fin m → ℝ),
    (∀ i, toReal (f i).inf ≤ x i ∧ x i ≤ toReal (f i).sup) →
      toReal (Taylm.prodBounds f).inf ≤ ∏ i, x i ∧
        ∏ i, x i ≤ toReal (Taylm.prodBounds f).sup := by -- --- PROOF ---
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

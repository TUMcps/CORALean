module

public import CORALean.Global.Cost
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ExhaustiveSearchCost

@[expose] public section

/-!
# `Zonotope.exhaustiveSearchCost_ops_le`

The count itself: at most four times `C(p, n) · p`, from `p = 1` on.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The count itself: at most four times `C(p, n) · p`, from `p = 1` on. -/
theorem Zonotope.exhaustiveSearchCost_ops_le (n p : ℕ) (hp : 1 ≤ p) :
    (Zonotope.exhaustiveSearchCost n p).ops ≤ 4 * (p.choose n * p) := by -- --- PROOF ---
  -- `log₂ C(p, n) ≤ p`, the binomial being at most `2ᵖ`
  have hlog : Nat.log 2 (p.choose n) ≤ p :=
    (Nat.log_mono_right (Nat.choose_le_two_pow p n)).trans (Nat.log_pow (by norm_num) p).le
  simp only [Zonotope.exhaustiveSearchCost, Cost.ops_add, Cost.sort]
  calc p.choose n * (2 * p) + p.choose n * (Nat.log 2 (p.choose n) + 1)
      ≤ p.choose n * (2 * p) + p.choose n * (p + p) := by gcongr
    _ = 4 * (p.choose n * p) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

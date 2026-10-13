module

public import CORALean.ContSet.Taylm.Real.Operations.Uminus
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNeg
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Taylm.uminus` encloses the negation
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.uminus_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uminus.Encloses fun t => -f t := by
  intro t ht
  have := h t ht
  simp only [Taylm.uminus, Taylm.poly, Taylm.polyOf_neg] at *
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

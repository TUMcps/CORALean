module

public import CORALean.ContSet.Taylm.Real.Operations.Pow
public import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter
public import CORALean.ContSet.Taylm.Real.Theorems.Basic

@[expose] public section

/-!
# `Taylm.pow` encloses the power
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.pow_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    ∀ k : ℕ, (T.pow k).Encloses fun t => f t ^ k := by
  intro k
  induction k with
  | zero => simpa only [Taylm.pow, pow_zero] using Taylm.const_outer (n := n) 1 T.maxOrder
  | succ k ih => simpa only [Taylm.pow, pow_succ] using Taylm.times_outer ih h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

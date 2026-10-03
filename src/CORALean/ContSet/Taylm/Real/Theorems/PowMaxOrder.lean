import CORALean.ContSet.Taylm.Real.Operations.Pow

/-!
# A power keeps the model's order

`pow 0` is the constant one at the model's order and every further factor is a `times` at the
same order, whose result takes the larger of the two.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.pow_maxOrder (T : Taylm n) (k : ℕ) : (T.pow k).maxOrder = T.maxOrder := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Taylm.pow, Taylm.times, ih]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

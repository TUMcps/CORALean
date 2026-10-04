import CORALean.ContSet.Interval.Real.Operations.EBox

/-!
# `Interval.Inf`

CORA's `interval.Inf(n)`: the interval `(-∞, ∞)ⁿ`, lower bound `-Inf(n,1)`, upper bound
`Inf(n,1)`. Its bounds are infinite, so the result is an `Interval.EBox`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.Inf (n : ℕ) : Interval.EBox n :=
  let lb : Fin n → EReal := fun _ => ⊥
  let ub : Fin n → EReal := fun _ => ⊤
  (lb, ub)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

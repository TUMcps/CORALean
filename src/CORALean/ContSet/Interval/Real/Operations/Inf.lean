module

public import CORALean.ContSet.Interval.Real.Operations.EBox

@[expose] public section

/-!
# `Interval.Inf`

CORA's `interval.Inf(n)`: the interval `(-∞, ∞)ⁿ`, lower bound `-Inf(n,1)`, upper bound
`Inf(n,1)`. Its bounds are infinite, so the result is an `Interval.EBox`.

## Inputs
* `n` – dimension

## Output
* extended box unbounded in every coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

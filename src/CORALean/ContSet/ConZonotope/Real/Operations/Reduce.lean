import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# `ConZonotope.reduce`

Above the requested order, the enclosing zonotope is reduced and the constraints
dropped; at or below it, nothing happens and the constraints survive. Dropping a
constraint enlarges the set, so both branches over-approximate.

CORA reduces the generators and eliminates constraints by separate rules, each
keeping the constraint block meaningful. Either would replace this without
touching the guarantee, which is stated for the operation and not for the rule.
`ConZonotope.reduceKeep` is the alternative that keeps the constraints.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConZonotope.reduce (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  if o * n < cZ.h then (cZ.zonotope.reduce o).conZonotope else cZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

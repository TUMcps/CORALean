import CORALean.ContSet.ConZonotope.Real.Operations.Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# `ConZonotope.reduce`

Above the requested order, the enclosing zonotope is reduced and the constraints
dropped; at or below it, nothing happens and the constraints survive. Dropping a
constraint enlarges the set, so both branches over-approximate.

CORA reduces the generators and eliminates constraints by separate rules, each
keeping the constraint block meaningful. Either would replace this without
touching the guarantee, which is stated for the operation and not for the rule.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ConZonotope.reduce (C : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  if o * n < C.h then (C.zonotope.reduce o).conZonotope else C

end CORALean.Real

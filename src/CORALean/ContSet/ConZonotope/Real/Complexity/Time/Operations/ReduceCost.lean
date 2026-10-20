module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `ConZonotope.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` past the order threshold drops to the enclosing
zonotope, reduces that, and reads the result back as a constrained zonotope with no constraints.
Both conversions repackage fields, each writing `n * (1 + h)` at most; the threshold branch returns
the operand, `n * (1 + h) + (r + re) * (h + 1)` scalars. The count is `Zonotope.reduceGirardCost`
and those writes. No linear program anywhere in it: a reduction that kept the constraints would have
to decide which coefficients they still admit, and this one throws them away first, a precision
decision that `Theorems/` states. Below the threshold the operation is the identity, so this bounds
every `o` at once.

## Inputs
* `n` – dimension
* `h` – number of generators
* `r` – number of inequalities
* `re` – number of equalities

## Output
* the cost of the order reduction
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.reduce`, at any order, costs at `Vec ℝ n` on `h` generators and a constraint
polytope of `r` inequality and `re` equality rows: the zonotope reduction, and the writes of
the two conversions and of the operand returned below the threshold. -/
def ConZonotope.reduceCost (n h r re : ℕ) : Cost :=
  Zonotope.reduceGirardCost n h + ⟨2 * (n * (1 + h)) + (r + re) * (h + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

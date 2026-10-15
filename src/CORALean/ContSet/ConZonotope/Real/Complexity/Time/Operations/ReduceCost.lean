module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `ConZonotope.reduceCost`

Asserted, not proved: `Operations/Reduce.lean` past the order threshold drops
to the enclosing zonotope, reduces *that*, and reads the result back as a
constrained zonotope with no constraints. Both conversions copy fields and
allocate, so the whole count is `Zonotope.reduceGirardCost`.

No linear program anywhere in it, which is the thing worth saying: a reduction
that kept the constraints would have to decide which coefficients they still
admit, and this one never asks, because it throws them away first. That is a
precision decision, not a cost decision, and what it gives up is an enclosure
`Theorems/` states rather than anything this file can see.

Below the threshold the operation is the identity, so this bounds every `o` at
once.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.reduce`, at any order, costs at `Vec ℝ n` on `h`
generators: the zonotope reduction, the two conversions being free. -/
def ConZonotope.reduceCost (n h : ℕ) : Cost := Zonotope.reduceGirardCost n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

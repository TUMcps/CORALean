module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `ZonoBundle.reduce`

CORA's `@zonoBundle/reduce`: every member is reduced to the order asked for, by the method asked
for, and all of them are kept. The method here is `Zonotope.reduce`'s, Girard's, CORA's default.

A bundle denotes an *intersection*, so enlarging each member enlarges the set, and the intersection
over the reduced members contains the original (the `Reduce` instance's `reduce_outer`, monotone in
the members). The bundle keeps its member count; only each member's generator count comes down, to
`o * n` at most (`reduce_order_le`).

## Inputs
* `zB` – zonotope bundle
* `o` – maximum order of each member

## Output
* bundle of the reduced members
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: each member of the bundle reduced to order `o`, none dropped. -/
noncomputable def ZonoBundle.reduce (zB : ZonoBundle (Vec ℝ n)) (o : ℕ) : ZonoBundle (Vec ℝ n) where
  k := zB.k
  Z := fun i => (zB.Z i).reduce o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

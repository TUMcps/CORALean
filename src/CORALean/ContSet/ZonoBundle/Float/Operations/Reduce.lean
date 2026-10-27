module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Reduce

@[expose] public section

/-!
# `ZonoBundle.reduce`, over a floating-point scalar

CORA's `@zonoBundle/reduce`, as over ℝ: every member is reduced to the order asked for by the float
`Zonotope.reduce`, Girard's rule, and all of them are kept. Each member boxes what it absorbs into
its own error box, so the bundle's rounding stays where the members put it.

The intersection over the reduced members contains the original (`reduce_outer`, through
`SetIntersection.memberwise_outer`); the member count is unchanged, and each member has at most
`o * n` generators (`reduce_order_le`).

## Inputs
* `zB` – float zonotope bundle
* `o` – maximum order of each member

## Output
* bundle of the reduced members
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: each member of the bundle reduced to order `o`, none dropped. -/
def ZonoBundle.reduce (zB : ZonoBundle (Vec 𝕋 n)) (o : ℕ) : ZonoBundle (Vec 𝕋 n) where
  k := zB.k
  Z := fun i => (zB.Z i).reduce o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

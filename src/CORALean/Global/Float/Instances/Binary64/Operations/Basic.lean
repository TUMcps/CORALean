module

public import CORALean.Global.Float.Instances.Binary64.Binary64
public import CORALean.Global.Float.Instances.Binary64.Operations.AddUp
public import CORALean.Global.Float.Instances.Binary64.Operations.MulUp

@[expose] public section

/-!
# `Global/Float/Instances/Binary64/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ========================================  `addDown`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace Binary64

/-- Negation flips the sign bit and nothing else, so this rounds down by rounding
its negation up. Definitional, so the guarantee in `Theorems` is the upward
assumption read through `toReal_neg`, needing no axiom of its own. -/
def addDown (a b : Float) : Float := -addUp (-a) (-b)

end Binary64

end CORALean.Float


-- ========================================  `maximum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace Binary64

/-- `Minimum`'s mirror: core's `max a b` is `if a ≤ b then b else a`, which drops a NaN in its
second argument, and this returns it. -/
def maximum (a b : Float) : Float :=
  -- core's `max` where either comparison holds, which is everywhere but at a NaN; there `a + b`
  if a ≤ b then b else if b < a then a else a + b

end Binary64

end CORALean.Float


-- ========================================  `minimum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace Binary64

/-- Core's `min a b` is `if a ≤ b then a else b`, which returns `b` when `a` is NaN, since every
comparison with a NaN is false: a NaN in the first argument would be dropped, and a run that left
the trusted range could end in a number. This returns the NaN instead. -/
def minimum (a b : Float) : Float :=
  -- core's `min` where either comparison holds, which is everywhere but at a NaN; there `a + b`
  if a ≤ b then a else if b < a then b else a + b

end Binary64

end CORALean.Float


-- ========================================  `mulDown`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace Binary64

/-- Negates one argument rather than two: a product changes sign with either
factor, where a sum needs both. Otherwise the reading is `AddDown`'s — the
upward assumption at `-a`, turned around by `toReal_neg`. -/
def mulDown (a b : Float) : Float := -mulUp (-a) b

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

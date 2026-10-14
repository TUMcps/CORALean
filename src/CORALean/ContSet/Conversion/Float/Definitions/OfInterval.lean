module

public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# Absorbing a box, over a floating-point scalar

The counterpart of `IntervalOuter`, and what puts a computed box back into
whatever is being propagated: a bias vector, a relaxation's error, an
approximation error.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Named for the source, alone among the conversions, the target having no name
to be called after. -/
class OfInterval (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec 𝕋 n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec 𝕋 n)) : construct I ⊆ construct (ofInterval I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

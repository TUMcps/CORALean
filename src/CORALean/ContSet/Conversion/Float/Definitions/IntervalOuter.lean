module

public import CORALean.ContSet.Capsule.Float.Instances
public import CORALean.ContSet.ConPolyZono.Float.Instances
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.VPolytope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# Enclosing itself in a box, over a floating-point scalar

The float counterpart of the exact layer's class: an algorithm that needs
coordinate bounds without naming the source asks for this, and a network's
activation layer is the caller that forces it — every neuron's relaxation is a
function of that neuron's range.

`𝕋` is an `outParam`, unlike anything in the exact layer, because the box comes
back in the scalar the representation stores rather than in ℝ; a caller writes
`IntervalOuter S` and the family it propagates says which scalar that is.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Named for the target, as every conversion is: `interval` is CORA's
`interval(S)`. -/
class IntervalOuter (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  interval {n : ℕ} : S n → Interval (Vec 𝕋 n)
  interval_outer {n : ℕ} (s : S n) : construct s ⊆ construct (interval s)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

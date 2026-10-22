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
# Boxes in and out of a representation, over a floating-point scalar

The float counterparts of the exact layer's classes. `𝕋` is an `outParam`, unlike anything in the
exact layer, because the box comes back in the scalar the representation stores rather than in ℝ; a
caller writes `IntervalOuter S` and the family it propagates says which scalar that is. A network's
activation layer is the caller that forces `IntervalOuter`, every neuron's relaxation being a
function of its range; `OfInterval` puts a computed box back, as a bias vector or an error.
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

/-- Named for the source, alone among the conversions, the target having no name
to be called after. -/
class OfInterval (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec 𝕋 n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec 𝕋 n)) : construct I ⊆ construct (ofInterval I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

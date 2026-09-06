import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# Enclosing itself in a box, over a floating-point scalar

The float counterpart of the exact layer's class: an algorithm that needs
coordinate bounds without naming the source asks for this, and a network's
activation layer is the caller that forces it — every neuron's relaxation is a
function of that neuron's range.

`𝕋` is an `outParam`, unlike anything in the exact layer, because the box comes
back in the scalar the representation stores rather than in ℝ; a caller writes
`IntervalOuter S` and the family it propagates says which scalar that is.

The instance list is the exact layer's, minus the polytopes for the same reason:
a box from halfspaces or vertices is `2n` linear programs, so `interval` there
takes certificates and is no function of the representation alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Named for the target, as every conversion is: `interval` is CORA's
`interval(S)`. -/
class IntervalOuter (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  interval {n : ℕ} : S n → Interval 𝕋 n
  interval_outer {n : ℕ} (s : S n) : construct s ⊆ construct (interval s)

/-- A box is its own. -/
instance : IntervalOuter (fun n => Interval 𝕋 n) 𝕋 where
  interval I := I
  interval_outer _ := subset_rfl

instance : IntervalOuter (fun n => Zonotope 𝕋 n) 𝕋 where
  interval Z := Z.interval
  interval_outer Z := Zonotope.interval_outer Z

instance : IntervalOuter (fun n => ConZonotope 𝕋 n) 𝕋 where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_outer C

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

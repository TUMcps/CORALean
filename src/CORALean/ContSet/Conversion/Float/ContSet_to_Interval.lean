import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
import CORALean.ContSet.Conversion.Float.ConPolyZono_to_Interval
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Capsule.Float.Instances
import CORALean.ContSet.ConPolyZono.Float.Instances
import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.VPolytope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Global.Float.Instances.Real.Instances

/-!
# Enclosing itself in a box, over a floating-point scalar

The float counterpart of the exact layer's class: an algorithm that needs
coordinate bounds without naming the source asks for this, and a network's
activation layer is the caller that forces it — every neuron's relaxation is a
function of that neuron's range.

`𝕋` is an `outParam`, unlike anything in the exact layer, because the box comes
back in the scalar the representation stores rather than in ℝ; a caller writes
`IntervalOuter S` and the family it propagates says which scalar that is.

The instance list is the exact layer's, minus `HPolytope`: a box from halfspaces
is `2n` linear programs, so `interval` there takes certificates and is no function
of the representation alone. A vertex list needs none (`boundProj`/`boundNegProj`).

An exact representation is one at `𝕋 := ℝ`, through its own class: that is what lets an
algorithm written once over the scalar run on `Real.Zonotope` as well as on a float one.
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

/-- A box is its own. -/
instance : IntervalOuter (fun n => Interval (Vec 𝕋 n)) 𝕋 where
  interval I := I
  interval_outer _ := subset_rfl

instance : IntervalOuter (fun n => Zonotope (Vec 𝕋 n)) 𝕋 where
  interval Z := Z.interval
  interval_outer Z := Zonotope.interval_contains Z

instance : IntervalOuter (fun n => ConZonotope 𝕋 (Vec 𝕋 n)) 𝕋 where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_contains C

instance : IntervalOuter (fun n => Capsule 𝕋 n) 𝕋 where
  interval C := C.interval
  interval_outer C := Capsule.interval_contains C

instance : IntervalOuter (fun n => ConPolyZono 𝕋 (Vec 𝕋 n)) 𝕋 where
  interval C := C.interval
  interval_outer C := ConPolyZono.interval_contains C

instance : IntervalOuter (fun n => PolyZonotope (Vec 𝕋 n)) 𝕋 where
  interval P := P.interval
  interval_outer P := PolyZonotope.interval_contains P

/-- The box of a vertex list: the bounds `boundProj`/`boundNegProj` of every coordinate. -/
instance : IntervalOuter (fun n => VPolytope (Vec 𝕋 n)) 𝕋 where
  interval P := P.interval
  interval_outer P := VPolytope.interval_contains P

/-- An exact representation boxes itself at `𝕋 := ℝ`, the box its exact class returns. -/
instance {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S] :
    IntervalOuter S ℝ where
  interval s := ⟨(Real.IntervalOuter.interval s).inf, (Real.IntervalOuter.interval s).sup⟩
  interval_outer s := Real.IntervalOuter.interval_outer s

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_Interval
public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# Enclosing itself in a box, asked for as a class

The pair where the source is any representation. An algorithm that needs
coordinate bounds — a network's activation layer does, for every neuron, before
it can relax anything — cannot name the source, so it asks for this instead, and
the instance list below is what answers.

Not every representation has one, and that is the point: `HPolytope` reaches
its box through `2n` linear programs, so its `interval` takes the certificates
as arguments and cannot be a total function of the representation alone. A pipeline
that wants them supplies the box itself.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- Named for the target, as every conversion is: `interval` is CORA's
`interval(S)`. -/
class IntervalOuter (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  interval {n : ℕ} : S n → Interval (Vec ℝ n)
  interval_outer {n : ℕ} (s : S n) : construct s ⊆ construct (interval s)

/-- A box is its own. -/
instance : IntervalOuter (fun n => Interval (Vec ℝ n)) where
  interval I := I
  interval_outer _ := subset_rfl

instance : IntervalOuter 𝒵 where
  interval Z := Z.interval
  interval_outer Z := Zonotope.interval_contains Z

instance : IntervalOuter (fun n => ConZonotope (Vec ℝ n)) where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_contains C

instance : IntervalOuter (fun n => Capsule n) where
  interval C := C.interval
  interval_outer C := Capsule.interval_contains C

instance : IntervalOuter (fun n => ConPolyZono (Vec ℝ n)) where
  interval C := C.interval
  interval_outer C := ConPolyZono.interval_contains C

instance : IntervalOuter (fun n => PolyZonotope (Vec ℝ n)) where
  interval P := P.interval
  interval_outer P := PolyZonotope.interval_contains P

/-- The box of a vertex list: the extreme coordinates of its vertices. -/
noncomputable instance : IntervalOuter (fun n => VPolytope (Vec ℝ n)) where
  interval P := P.interval
  interval_outer P := VPolytope.interval_contains P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

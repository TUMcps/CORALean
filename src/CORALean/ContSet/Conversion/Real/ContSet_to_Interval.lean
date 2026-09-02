import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Enclosing itself in a box, asked for as a class

The pair where the source is any representation. An algorithm that needs
coordinate bounds — a network's activation layer does, for every neuron, before
it can relax anything — cannot name the source, so it asks for this instead, and
the instance list below is what answers.

Not every representation has one, and that is the point: `HPolytope` and
`VPolytope` reach their box through `2n` linear programs, so their `interval`
takes the certificates as arguments and cannot be a total function of the
representation alone. A pipeline that wants them supplies the box itself.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

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
  interval_outer Z := Zonotope.interval_outer Z

instance : IntervalOuter (fun n => ConZonotope (Vec ℝ n)) where
  interval C := C.interval
  interval_outer C := ConZonotope.interval_outer C

end CORALean.Real

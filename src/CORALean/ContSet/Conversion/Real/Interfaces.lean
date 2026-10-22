module

public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# Boxes in and out of a representation, asked for as classes

`IntervalOuter`: the source is any representation. An algorithm that needs coordinate bounds, as a
network's activation layer does for every neuron, cannot name the source, so it asks for this and
the instances answer. `OfInterval` is its counterpart, putting a computed box back into whatever is
propagated (a bias vector, an approximation error); named for the source, alone among the
conversions, the target having no name to be called after.
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

/-- A representation family that can hold a box: `ofInterval` gives a set containing the box. -/
class OfInterval (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec ℝ n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec ℝ n)) :
    construct I ⊆ construct (ofInterval I)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

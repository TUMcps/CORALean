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
# Enclosing itself in a box, asked for as a class

The pair where the source is any representation. An algorithm that needs
coordinate bounds — a network's activation layer does, for every neuron, before
it can relax anything — cannot name the source, so it asks for this instead, and
the instance list below is what answers.
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

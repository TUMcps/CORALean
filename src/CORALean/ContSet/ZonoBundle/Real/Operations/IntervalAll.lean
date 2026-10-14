module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ZonoBundle.intervalAll`: the box of the whole bundle

CORA's `@zonoBundle/interval`: the intersection of every member's box, in order, which is a box
of the whole bundle and tighter than any one member's (`ZonoBundle.interval`). It needs a member
to start from, so the bundle is asked to have one; CORA returns the empty box for none, which
here would be wrong, a bundle of no members being the whole space.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The intersection of every member's box, starting from the first member's. -/
def ZonoBundle.intervalAll (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) : Interval (Vec ℝ n) :=
  (List.finRange zB.k).foldl (fun I i => Interval.intersection I (zB.interval i))
    (zB.interval ⟨0, hk⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Intersection

/-!
# `ZonoBundle.intervalAll`: the box of the whole bundle

CORA's `@zonoBundle/interval`: the intersection of every member's box, in order, which is a box
of the whole bundle and tighter than any one member's (`ZonoBundle.interval`). It needs a member
to start from, so the bundle is asked to have one; CORA returns the empty box for none, which
here would be wrong, a bundle of no members being the whole space.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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

module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.ContSet.Definitions.SupportFunc

@[expose] public section

/-!
# `ZonoBundle.intervalSupportFunc`: the bundle's box by its support function

CORA's `interval` of a bundle intersects the members' boxes (`intervalAll`): each member's box is
its support function in the directions `±eᵢ`, cheap to read off its generators, but the
intersection of the boxes is in general larger than the box of the intersection. This is the
latter: the support function of the intersection itself in `eᵢ` and `-eᵢ`, so `supᵢ` is the
largest `xᵢ` over the bundle and `infᵢ` the least. Over ℝ it is a specification, noncomputable;
the float layer computes it by the bundle's linear program (`ZonoBundle.boundDotLP`).

At `k = 0` the bundle is the whole space and the support function `+∞`, read as `0` by
`EReal.toReal`: the theorems ask for a member, and the exact one for a point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle's box from the support function of the intersection in the directions `±eᵢ`. -/
noncomputable def ZonoBundle.intervalSupportFunc (zB : ZonoBundle (Vec ℝ n)) : Interval (Vec ℝ n)
    where
  inf i := -(supportFunc zB.construct (-LinearMap.proj i)).toReal
  sup i := (supportFunc zB.construct (LinearMap.proj i)).toReal

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

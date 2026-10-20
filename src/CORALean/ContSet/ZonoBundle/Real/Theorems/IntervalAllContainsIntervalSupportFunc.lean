module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalSupportFuncExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContains

@[expose] public section

/-!
# CORA's box of a bundle contains the support-function box

`intervalAll`, the intersection of the members' boxes, is a box holding the bundle, and the
support-function box is the least of those (`intervalSupportFunc_exact`): the support function of
the intersection is never worse than CORA's member-wise box, and strictly tighter wherever the
members' boxes overlap beyond the intersection.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – the bundle has a member
* `hne` – the bundle is nonempty

## Conclusion
* the support-function box is contained in the plain box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intersection of the members' boxes contains the support-function box. -/
theorem ZonoBundle.intervalAll_contains_intervalSupportFunc (zB : ZonoBundle (Vec ℝ n))
    (hk : 0 < zB.k) (hne : zB.construct.Nonempty) :
    zB.intervalSupportFunc.construct ⊆ (zB.intervalAll hk).construct := by
  rw [zB.intervalSupportFunc_exact hk hne]
  exact Set.iInter_subset_of_subset ⟨_, zB.intervalAll_contains hk⟩ subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
